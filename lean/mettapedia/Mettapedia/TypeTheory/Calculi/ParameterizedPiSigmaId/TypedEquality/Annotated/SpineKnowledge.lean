import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.RootPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ComputationSchemas

/-!
# What a constant spine knows about its metavariables

A constant declared at a telescope, applied to a first-order spine, hands each
argument the type of the corresponding entry with the earlier arguments
substituted. `patternKnowledge` records that type at each metavariable that
occurs in the argument, and records nothing where the metavariable does not
occur.

The type still to be synthesized after `j` arguments is a term over `j`
variables. `Remaining` relates that term to the declared telescope without
casting a context of `j + 1` variables into a context of `(j + 1)` variables.
After a spine `ts` shorter than the telescope, elaboration synthesizes the
dependent function whose domain is the next entry at `ts` and whose codomain is
the substituted remaining type: instantiating that codomain at the next
argument is the substituted remaining type one entry further on.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open TelescopeAbstraction (closeType)

variable {Head : Type}

/-! ## Closed annotated terms -/

/-- Renaming by the empty renaming leaves a closed annotated term fixed. -/
theorem rename_elim0_id (t : CTm Head 0) : CTm.rename Fin.elim0 t = t := by
  have h : ∀ i : Fin 0, Fin.elim0 i = idRen i := fun i => i.elim0
  rw [CTm.rename_ext h, CTm.rename_id]

/-- Substituting into a closed annotated term is embedding it. -/
theorem subst_closed {m : Nat} (σ : CSub Head 0 m) (t : CTm Head 0) :
    CTm.subst σ t = CTm.liftClosed t := by
  have h := CTm.subst_liftClosed σ t
  unfold CTm.liftClosed at h
  rw [rename_elim0_id t] at h
  unfold CTm.liftClosed
  exact h

/-- The substitution that sends the newest variable to `N` and the rest along `σ`. -/
def subCons {n m : Nat} (N : CTm Head m) (σ : CSub Head n m) : CSub Head (n + 1) m :=
  Fin.cases N σ

/-- Opening a substituted binder at `N` is substituting the extended substitution. -/
theorem inst0_subst_liftSub {n m : Nat} (N : CTm Head m) (σ : CSub Head n m)
    (B : CTm Head (n + 1)) :
    CTm.inst0 N (B.subst (CTm.liftSub σ)) = B.subst (subCons N σ) := by
  unfold CTm.inst0
  rw [CTm.subst_comp]
  apply CTm.subst_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact CTm.inst0_rename_wk N (σ j)

theorem liftTm_pi {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) :
    liftTm (.pi A B) = .pi (liftTm A) (liftTm B) := rfl

/-! ## List access -/

theorem getD_append_left {α : Type} (ts us : List α) (i : Nat) (d : α) (hi : i < ts.length) :
    (ts ++ us).getD i d = ts.getD i d := by
  induction ts generalizing i with
  | nil => cases hi
  | cons _ as ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

theorem getD_concat_last {α : Type} (ts : List α) (a d : α) :
    (ts ++ [a]).getD ts.length d = a := by
  induction ts with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem lt_of_getElem?_some {α : Type} {ts : List α} {j : Nat} {t : α}
    (h : ts[j]? = some t) : j < ts.length := by
  induction ts generalizing j with
  | nil => cases h
  | cons _ as ih =>
      cases j with
      | zero => exact Nat.zero_lt_succ as.length
      | succ j => exact Nat.succ_lt_succ (ih h)

theorem getElem?_append_left {α : Type} (ts us : List α) (j : Nat) (hj : j < ts.length) :
    (ts ++ us)[j]? = ts[j]? := by
  induction ts generalizing j with
  | nil => cases hj
  | cons _ as ih =>
      cases j with
      | zero => rfl
      | succ j => exact ih j (Nat.lt_of_succ_lt_succ hj)

theorem getElem?_concat_last {α : Type} (ts : List α) (a : α) :
    (ts ++ [a])[ts.length]? = some a := by
  induction ts with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem exists_getElem?_of_mem {α : Type} {t : α} {ts : List α} (h : t ∈ ts) :
    ∃ j : Nat, ts[j]? = some t := by
  induction ts with
  | nil => cases h
  | cons _ _ ih =>
      obtain rfl | hmem := List.mem_cons.mp h
      · exact ⟨0, rfl⟩
      · obtain ⟨j, hj⟩ := ih hmem
        exact ⟨j + 1, hj⟩

/-! ## The type remaining after a prefix of the telescope -/

/-- `R` is the type still open after the first `j` entries of the telescope
`entry`, whose body at `n` is `C`. -/
inductive Remaining (entry : (j : Nat) → Tm Head j) (n : Nat) (C : Tm Head n) :
    (j : Nat) → Tm Head j → Prop
  | all : Remaining entry n C n C
  | before {j : Nat} {R : Tm Head (j + 1)} :
      Remaining entry n C (j + 1) R → Remaining entry n C j (.pi (entry j) R)

theorem closeType_remaining {entry : (j : Nat) → Tm Head j} {n : Nat} {C : Tm Head n}
    {j : Nat} {R : Tm Head j} (h : Remaining entry n C j R) :
    closeType (Normalization.ofEntries entry j) R =
      closeType (Normalization.ofEntries entry n) C := by
  induction h with
  | all => rfl
  | before _ ih =>
      rw [← Normalization.closeType_ofEntries_succ]
      exact ih

theorem remaining_of_le_aux (entry : (j : Nat) → Tm Head j) (n : Nat) (C : Tm Head n)
    (d : Nat) : ∀ j, n - j = d → j ≤ n → ∃ R : Tm Head j, Remaining entry n C j R := by
  induction d with
  | zero =>
      intro j hd hj
      have hjEq : j = n := Nat.le_antisymm hj (Nat.sub_eq_zero_iff_le.mp hd)
      cases hjEq
      exact ⟨C, .all⟩
  | succ d ih =>
      intro j hd hj
      have hn : n = j + (d + 1) := (Nat.sub_eq_iff_eq_add' hj).mp hd
      have hj1 : j + 1 ≤ n := by
        rw [hn]
        exact Nat.add_le_add_left (Nat.le_add_left 1 d) j
      have hsub : n - (j + 1) = d := by
        rw [hn, Nat.add_comm d 1, ← Nat.add_assoc]
        exact Nat.add_sub_cancel_left (j + 1) d
      obtain ⟨R, hR⟩ := ih (j + 1) hsub hj1
      exact ⟨.pi (entry j) R, .before hR⟩

theorem remaining_of_le (entry : (j : Nat) → Tm Head j) (n : Nat) (C : Tm Head n)
    (j : Nat) (hj : j ≤ n) : ∃ R : Tm Head j, Remaining entry n C j R :=
  remaining_of_le_aux entry n C (n - j) j rfl hj

theorem remaining_pi {entry : (j : Nat) → Tm Head j} {n : Nat} {C : Tm Head n}
    {j : Nat} {R : Tm Head j} (h : Remaining entry n C j R) (hj : j < n) :
    ∃ R' : Tm Head (j + 1), Remaining entry n C (j + 1) R' ∧ R = .pi (entry j) R' := by
  cases h with
  | all => exact False.elim (Nat.lt_irrefl _ hj)
  | before hR => exact ⟨_, hR, rfl⟩

/-! ## Entries at a spine -/

/-- The substitution sending each variable of an entry of arity `k` to the
corresponding earlier argument of `ts`. Variable `0` is the newest, which is
the last of those arguments. -/
def argSub {N : Nat} (ts : List (Tm Head N)) (k : Nat) : CSub Head k N :=
  fun i => liftTm (listSub k ts i)

/-- The type of entry `j` with the first `j` arguments of `ts` substituted. -/
def argType (entry : (j : Nat) → Tm Head j) {N : Nat} (ts : List (Tm Head N))
    (j : Nat) : CTm Head N :=
  (liftTm (entry j)).subst (argSub ts j)

theorem listSub_append {N : Nat} (j : Nat) (ts us : List (Tm Head N)) (hj : j ≤ ts.length)
    (i : Fin j) : listSub j (ts ++ us) i = listSub j ts i := by
  have hlt : j - 1 - i.val < ts.length := by
    have hi : i.val + 1 ≤ j := Nat.succ_le_of_lt i.isLt
    have hsubJ : j - (i.val + 1) < j := Nat.sub_lt_of_pos_le (Nat.succ_pos i.val) hi
    have hidx : j - 1 - i.val = j - (i.val + 1) := by
      rw [Nat.sub_sub]
      exact congrArg (fun k => j - k) (Nat.add_comm 1 i.val)
    exact Nat.lt_of_lt_of_le (hidx.symm ▸ hsubJ) hj
  unfold listSub
  exact getD_append_left ts us (j - 1 - i.val) _ hlt

theorem argType_append (entry : (j : Nat) → Tm Head j) {N : Nat}
    (ts us : List (Tm Head N)) (j : Nat) (hj : j ≤ ts.length) :
    argType entry (ts ++ us) j = argType entry ts j := by
  unfold argType
  apply CTm.subst_ext
  intro i
  exact congrArg liftTm (listSub_append j ts us hj i)

theorem subCons_argSub {N : Nat} (ts : List (Tm Head N)) (a : Tm Head N)
    (i : Fin (ts.length + 1)) :
    subCons (liftTm a) (argSub ts ts.length) i =
      argSub (ts ++ [a]) (ts.length + 1) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · unfold subCons argSub listSub
    rw [Fin.cases_zero]
    have hidx : (ts.length + 1) - 1 - ((0 : Fin (ts.length + 1)).val) = ts.length := by
      rw [Fin.val_zero, Nat.sub_zero]
      exact Nat.add_sub_cancel ts.length 1
    rw [hidx, getD_concat_last]
  · unfold subCons argSub listSub
    rw [Fin.cases_succ]
    have hidx : (ts.length + 1) - 1 - j.succ.val = ts.length - 1 - j.val := by
      rw [Fin.val_succ, Nat.add_sub_cancel, ← Nat.sub_sub]
      exact Nat.sub_right_comm ts.length j.val 1
    have hlt : ts.length - 1 - j.val < ts.length := by
      have hpos : 0 < ts.length := Nat.zero_lt_of_lt j.isLt
      exact Nat.lt_of_le_of_lt (Nat.sub_le (ts.length - 1) j.val)
        (Nat.sub_lt hpos (Nat.zero_lt_succ 0))
    rw [hidx]
    exact (congrArg liftTm
      (getD_append_left ts [a] (ts.length - 1 - j.val) Normalization.defaultTm hlt)).symm

theorem firstOrder_appSpine {N : Nat} (g : Tm Head N) (ts : List (Tm Head N))
    (hg : firstOrder g = true) (h : ∀ t ∈ ts, firstOrder t = true) :
    firstOrder (Normalization.appSpine g ts) = true := by
  induction ts generalizing g with
  | nil =>
      rw [Normalization.appSpine_nil]
      exact hg
  | cons a as ih =>
      rw [Normalization.appSpine_cons]
      exact ih (.app g a)
        (by
          rw [firstOrder, hg, h a (List.mem_cons.mpr (Or.inl rfl))]
          rfl)
        (fun t ht => h t (List.mem_cons.mpr (Or.inr ht)))

theorem elaborate_app_pi (decls : DeclName → Option (CTm Head 0)) {N : Nat}
    {g a : Tm Head N} (fog : firstOrder g = true) (foa : firstOrder a = true)
    {D : CTm Head N} {B : CTm Head (N + 1)}
    (h : (elaborate decls Knowledge.empty none none g).2 = some (.pi D B)) :
    (elaborate decls Knowledge.empty none none (.app g a)).2 =
      some (CTm.inst0 (liftTm a) B) := by
  rw [elaborate_app_type decls fog foa, h]

theorem patternDomain_of_pi (decls : DeclName → Option (CTm Head 0)) {N : Nat}
    {g : Tm Head N} {D : CTm Head N} {B : CTm Head (N + 1)}
    (h : (elaborate decls Knowledge.empty none none g).2 = some (.pi D B)) :
    (match (elaborate decls Knowledge.empty none none g).2 with
      | some (.pi D _) => some D
      | _ => none) = some D := by
  rw [h]

theorem merge_right_of_none {n : Nat} (K K' : Knowledge Head n) (v : Fin n)
    (h : K' v = none) : K.merge K' v = K v := by
  unfold Knowledge.merge
  cases hK : K v with
  | some _ => rfl
  | none => rw [h]

theorem merge_left_of_none {n : Nat} {K K' : Knowledge Head n} {v : Fin n}
    (h : K v = none) : K.merge K' v = K' v := by
  unfold Knowledge.merge
  rw [h]

theorem merge_left_of_some {n : Nat} {K K' : Knowledge Head n} {v : Fin n} {T : CTm Head n}
    (h : K v = some T) : K.merge K' v = some T := by
  simp only [Knowledge.merge, h]

/-- Knowledge at an application is the merge of the function's knowledge with
the argument's knowledge at the domain the function synthesizes. -/
theorem patternKnowledge_app {n : Nat} (decls : DeclName → Option (CTm Head 0))
    (expected : Option (CTm Head n)) (f a : Tm Head n) (v : Fin n) :
    patternKnowledge decls expected (.app f a) v =
      ((patternKnowledge decls none f).merge
        (patternKnowledge decls
          (match (elaborate decls Knowledge.empty none none f).2 with
            | some (.pi D _) => some D
            | _ => none) a)) v := rfl

theorem variableMultiplicity_var_ne {n : Nat} {i v : Fin n} (hne : i ≠ v) :
    AlgebraicSchema.variableMultiplicity v (.var i : Tm Head n) = 0 := by
  simp only [AlgebraicSchema.variableMultiplicity, if_neg hne]

theorem variableMultiplicity_app_const_var {n : Nat} (c : DeclName) {i v : Fin n}
    (hne : i ≠ v) :
    AlgebraicSchema.variableMultiplicity v (.app (.const c) (.var i) : Tm Head n) = 0 := by
  simp only [AlgebraicSchema.variableMultiplicity, if_neg hne, Nat.zero_add]

/-! ## No occurrence, no knowledge -/

/-- A metavariable that does not occur in a first-order term is not given a type. -/
theorem patternKnowledge_absent (decls : DeclName → Option (CTm Head 0)) {n : Nat}
    {expected : Option (CTm Head n)} {t : Tm Head n} (v : Fin n)
    (fo : firstOrder t = true) (hocc : AlgebraicSchema.variableMultiplicity v t = 0) :
    patternKnowledge decls expected t v = none := by
  induction t with
  | var i =>
      simp only [AlgebraicSchema.variableMultiplicity] at hocc
      have hne : i ≠ v := by
        intro hv
        rw [if_pos hv] at hocc
        exact Nat.one_ne_zero hocc
      simp only [patternKnowledge, if_neg hne.symm]
  | const => rfl
  | head => rfl
  | app f a ihf iha =>
      simp only [firstOrder, Bool.and_eq_true] at fo
      simp only [AlgebraicSchema.variableMultiplicity, Nat.add_eq_zero_iff] at hocc
      rw [patternKnowledge_app, merge_right_of_none _ _ v (iha v fo.2 hocc.2)]
      exact ihf v fo.1 hocc.1
  | refl a ih =>
      simp only [AlgebraicSchema.variableMultiplicity] at hocc
      unfold patternKnowledge
      exact ih v fo hocc
  | pi => cases fo
  | sigma => cases fo
  | id => cases fo
  | lam => cases fo
  | pair => cases fo
  | fst => cases fo
  | snd => cases fo

/-! ## A declared constant -/

section Spine

variable (decls : DeclName → Option (CTm Head 0)) (f : DeclName) (n : Nat)
variable (entry : (j : Nat) → Tm Head j) (C : Tm Head n)
variable (declared : decls f = some (liftTm (closeType (Normalization.ofEntries entry n) C)))

theorem patternKnowledge_spine_expected {N : Nat} (ts : List (Tm Head N))
    (e1 e2 : Option (CTm Head N)) (v : Fin N) :
    patternKnowledge decls e1 (Normalization.appSpine (.const f) ts) v =
      patternKnowledge decls e2 (Normalization.appSpine (.const f) ts) v := by
  refine List.reverseRecOn
    (motive := fun ts => ∀ e1 e2, patternKnowledge decls e1
      (Normalization.appSpine (.const f) ts) v =
        patternKnowledge decls e2 (Normalization.appSpine (.const f) ts) v)
    ts ?_ ?_ e1 e2
  · intro e1 e2
    rfl
  · intro ts a _ e1 e2
    rw [Normalization.appSpine_concat]
    rfl

/-- A metavariable absent from every argument of a constant spine is not given a type. -/
theorem patternKnowledge_spine_absent {N : Nat} (ts : List (Tm Head N))
    (fo : ∀ t ∈ ts, firstOrder t = true) (v : Fin N)
    (habs : ∀ t ∈ ts, AlgebraicSchema.variableMultiplicity v t = 0)
    (expected : Option (CTm Head N)) :
    patternKnowledge decls expected (Normalization.appSpine (.const f) ts) v = none := by
  refine List.reverseRecOn
    (motive := fun ts =>
      (∀ t ∈ ts, firstOrder t = true) →
      (∀ t ∈ ts, AlgebraicSchema.variableMultiplicity v t = 0) →
      ∀ expected, patternKnowledge decls expected
        (Normalization.appSpine (.const f) ts) v = none)
    ts ?_ ?_ fo habs expected
  · intro _ _ expected
    simp only [Normalization.appSpine_nil, patternKnowledge, Knowledge.empty]
  · intro ts a ih fo habs expected
    have foTs : ∀ t ∈ ts, firstOrder t = true :=
      fun t ht => fo t (List.mem_append_left [a] ht)
    have habsTs : ∀ t ∈ ts, AlgebraicSchema.variableMultiplicity v t = 0 :=
      fun t ht => habs t (List.mem_append_left [a] ht)
    have foA : firstOrder a = true :=
      fo a (List.mem_append_right ts (List.mem_singleton_self a))
    have ha0 : AlgebraicSchema.variableMultiplicity v a = 0 :=
      habs a (List.mem_append_right ts (List.mem_singleton_self a))
    rw [Normalization.appSpine_concat, patternKnowledge_app,
      merge_right_of_none _ _ v (patternKnowledge_absent decls (t := a) v foA ha0)]
    exact ih foTs habsTs none

include C declared

/-- After the arguments `ts`, elaboration synthesizes the remaining type at
`ts.length`, with those arguments substituted. -/
theorem spine_type {N : Nat} (ts : List (Tm Head N))
    (fo : ∀ t ∈ ts, firstOrder t = true) (hlen : ts.length ≤ n) :
    ∃ R : Tm Head ts.length, Remaining entry n C ts.length R ∧
      (elaborate decls Knowledge.empty none none
        (Normalization.appSpine (.const f) ts)).2 =
        some ((liftTm R).subst (argSub ts ts.length)) := by
  refine List.reverseRecOn
    (motive := fun ts =>
      (∀ t ∈ ts, firstOrder t = true) → ts.length ≤ n →
      ∃ R : Tm Head ts.length, Remaining entry n C ts.length R ∧
        (elaborate decls Knowledge.empty none none
          (Normalization.appSpine (.const f) ts)).2 =
          some ((liftTm R).subst (argSub ts ts.length)))
    ts ?_ ?_ fo hlen
  · intro _ _
    obtain ⟨R, hR⟩ := remaining_of_le entry n C 0 (Nat.zero_le n)
    have hRdef : R = closeType (Normalization.ofEntries entry n) C := by
      have h := closeType_remaining hR
      simp only [Normalization.ofEntries, closeType] at h
      exact h
    refine ⟨R, hR, ?_⟩
    simp only [Normalization.appSpine_nil, elaborate, declared, ← hRdef]
    exact congrArg some (subst_closed (argSub ([] : List (Tm Head N)) 0) (liftTm R)).symm
  · intro ts a ih fo hlen
    have hlen1 : (ts ++ [a]).length = ts.length + 1 := by
      simp only [List.length_append, List.length_singleton]
    have hlenTs : ts.length ≤ n := by
      rw [hlen1] at hlen
      exact Nat.le_of_succ_le hlen
    have hlt : ts.length < n := by
      rw [hlen1] at hlen
      exact Nat.lt_of_succ_le hlen
    have foTs : ∀ t ∈ ts, firstOrder t = true :=
      fun t ht => fo t (List.mem_append_left [a] ht)
    have foA : firstOrder a = true :=
      fo a (List.mem_append_right ts (List.mem_singleton_self a))
    obtain ⟨R, hR, hsynth⟩ := ih foTs hlenTs
    obtain ⟨R', hR', rfl⟩ := remaining_pi hR hlt
    rw [hlen1]
    refine ⟨R', hR', ?_⟩
    rw [Normalization.appSpine_concat]
    have foSpine : firstOrder (Normalization.appSpine (.const f) ts) = true :=
      firstOrder_appSpine (.const f) ts rfl foTs
    have hshape :
        (liftTm (.pi (entry ts.length) R')).subst (argSub ts ts.length) =
          .pi (argType entry ts ts.length)
            ((liftTm R').subst (CTm.liftSub (argSub ts ts.length))) := rfl
    rw [hshape] at hsynth
    rw [elaborate_app_pi decls foSpine foA hsynth, inst0_subst_liftSub]
    apply congrArg some
    apply CTm.subst_ext
    intro i
    exact subCons_argSub ts a i

/-- **The type a spine synthesizes.** For a first-order spine shorter than the
telescope, elaboration synthesizes a dependent function type whose domain is
the next entry at the arguments so far. The codomain is the remaining type one
entry further on, substituted under the lifted argument substitution: the next
instantiation opens that codomain at the next argument. -/
theorem spine_synthesizes {N : Nat} (ts : List (Tm Head N))
    (fo : ∀ t ∈ ts, firstOrder t = true) (hlen : ts.length < n) :
    ∃ B : CTm Head (N + 1),
      (elaborate decls Knowledge.empty none none
        (Normalization.appSpine (.const f) ts)).2 =
        some (.pi (argType entry ts ts.length) B) ∧
      ∃ R : Tm Head (ts.length + 1), Remaining entry n C (ts.length + 1) R ∧
        B = (liftTm R).subst (CTm.liftSub (argSub ts ts.length)) := by
  obtain ⟨R0, hR0, hsynth⟩ := spine_type decls f n entry C declared ts fo (Nat.le_of_lt hlen)
  obtain ⟨R, hR, rfl⟩ := remaining_pi hR0 hlen
  refine ⟨(liftTm R).subst (CTm.liftSub (argSub ts ts.length)), ?_, R, hR, rfl⟩
  rw [hsynth]
  rfl

/-- **The knowledge of a spine.** A metavariable that occurs in argument `j` and
in no other argument is known there exactly as it is known in that argument
checked at the entry type. The stated absence condition is the one used: the
merge keeps the first `some`, and an argument that does not contain the
metavariable contributes `none`. -/
theorem spine_knowledge {N : Nat} (ts : List (Tm Head N))
    (fo : ∀ t ∈ ts, firstOrder t = true) (hlen : ts.length ≤ n) (j : Nat)
    (t : Tm Head N) (ht : ts[j]? = some t) (v : Fin N)
    (alone : ∀ (j' : Nat) (t' : Tm Head N), j' ≠ j → ts[j']? = some t' →
      AlgebraicSchema.variableMultiplicity v t' = 0)
    (expected : Option (CTm Head N)) :
    patternKnowledge decls expected (Normalization.appSpine (.const f) ts) v =
      patternKnowledge decls (some (argType entry ts j)) t v := by
  refine List.reverseRecOn
    (motive := fun ts =>
      (∀ t ∈ ts, firstOrder t = true) → ts.length ≤ n →
      ∀ (j : Nat) (t : Tm Head N) (ht : ts[j]? = some t) (v : Fin N)
        (alone : ∀ (j' : Nat) (t' : Tm Head N), j' ≠ j → ts[j']? = some t' →
          AlgebraicSchema.variableMultiplicity v t' = 0)
        (expected : Option (CTm Head N)),
        patternKnowledge decls expected (Normalization.appSpine (.const f) ts) v =
          patternKnowledge decls (some (argType entry ts j)) t v)
    ts ?_ ?_ fo hlen j t ht v alone expected
  · intro _ _ j t ht _ _ _
    cases ht
  · intro ts a ih fo hlen j t ht v alone expected
    have hlen1 : (ts ++ [a]).length = ts.length + 1 := by
      simp only [List.length_append, List.length_singleton]
    have foTs : ∀ t ∈ ts, firstOrder t = true :=
      fun t ht => fo t (List.mem_append_left [a] ht)
    have foA : firstOrder a = true :=
      fo a (List.mem_append_right ts (List.mem_singleton_self a))
    have hlenTs : ts.length ≤ n := by
      rw [hlen1] at hlen
      exact Nat.le_of_succ_le hlen
    cases hpos : decide (j = ts.length) with
    | true =>
        have hj : j = ts.length := of_decide_eq_true hpos
        have hlt : ts.length < n := by
          rw [hlen1] at hlen
          exact Nat.lt_of_succ_le hlen
        subst hj
        have htA := getElem?_concat_last ts a
        have hta : t = a := by
          have heq := ht.symm.trans htA
          injection heq
        rw [hta]
        obtain ⟨B, hsynth, _, _, _⟩ :=
          spine_synthesizes decls f n entry C declared ts foTs hlt
        have hdom := patternDomain_of_pi decls hsynth
        have habsent : patternKnowledge decls none
            (Normalization.appSpine (.const f) ts) v = none := by
          refine patternKnowledge_spine_absent decls f ts foTs v ?_ none
          intro t' ht'
          obtain ⟨j', hj'⟩ := exists_getElem?_of_mem ht'
          have hj'lt := lt_of_getElem?_some hj'
          exact alone j' t' (Nat.ne_of_lt hj'lt)
            (by rw [getElem?_append_left ts [a] j' hj'lt]; exact hj')
        rw [Normalization.appSpine_concat, patternKnowledge_app,
          merge_left_of_none habsent, hdom,
          argType_append entry ts [a] ts.length (Nat.le_refl _)]
    | false =>
        have hjne : j ≠ ts.length := of_decide_eq_false hpos
        have hjltAll := lt_of_getElem?_some ht
        rw [hlen1] at hjltAll
        have hjle : j ≤ ts.length := Nat.le_of_lt_succ hjltAll
        have hjlt : j < ts.length := Nat.lt_of_le_of_ne hjle hjne
        have htTs : ts[j]? = some t := by
          rw [← getElem?_append_left ts [a] j hjlt]
          exact ht
        have aloneTs : ∀ (j' : Nat) (t' : Tm Head N), j' ≠ j → ts[j']? = some t' →
            AlgebraicSchema.variableMultiplicity v t' = 0 := by
          intro j' t' hne ht'
          have hj'lt := lt_of_getElem?_some ht'
          exact alone j' t' hne (by
            rw [getElem?_append_left ts [a] j' hj'lt]
            exact ht')
        have ihv := ih foTs hlenTs j t htTs v aloneTs expected
        have hleft : patternKnowledge decls none
            (Normalization.appSpine (.const f) ts) v =
            patternKnowledge decls (some (argType entry ts j)) t v :=
          (patternKnowledge_spine_expected decls f ts none expected v).trans ihv
        have ha0 : AlgebraicSchema.variableMultiplicity v a = 0 :=
          alone ts.length a hjne.symm (getElem?_concat_last ts a)
        have haNone : patternKnowledge decls
            (match (elaborate decls Knowledge.empty none none
              (Normalization.appSpine (.const f) ts)).2 with
              | some (.pi D _) => some D
              | _ => none) a v = none :=
          patternKnowledge_absent decls (t := a) v foA ha0
        rw [Normalization.appSpine_concat, patternKnowledge_app,
          merge_right_of_none _ _ v haNone, hleft,
          argType_append entry ts [a] j (Nat.le_of_lt hjlt)]

/-- A metavariable standing alone as argument `j` is known at that entry's type. -/
theorem spine_knowledge_var {N : Nat} (ts : List (Tm Head N))
    (fo : ∀ t ∈ ts, firstOrder t = true) (hlen : ts.length ≤ n) (j : Nat) (v : Fin N)
    (ht : ts[j]? = some (.var v))
    (alone : ∀ (j' : Nat) (t' : Tm Head N), j' ≠ j → ts[j']? = some t' →
      AlgebraicSchema.variableMultiplicity v t' = 0)
    (expected : Option (CTm Head N)) :
    patternKnowledge decls expected (Normalization.appSpine (.const f) ts) v =
      some (argType entry ts j) := by
  rw [spine_knowledge decls f n entry C declared ts fo hlen j (.var v) ht v alone expected]
  unfold patternKnowledge
  exact if_pos rfl

end Spine

/-! ## Examples -/

namespace SpineExamples

section Dependent

def depEntry : (j : Nat) → Tm Head j
  | 0 => .const (Lean.Name.mkSimple "A")
  | 1 => .var 0
  | _ + 2 => .const (Lean.Name.mkSimple "T")

def depC : Tm Head 2 := .const (Lean.Name.mkSimple "B")

def depF : DeclName := Lean.Name.mkSimple "f"

def depDecls (c : DeclName) : Option (CTm Head 0) :=
  if c = depF then some (liftTm (closeType (Normalization.ofEntries depEntry 2) depC)) else none

theorem depDeclared :
    (depDecls depF : Option (CTm Head 0)) =
      some (liftTm (closeType (Normalization.ofEntries depEntry 2) depC)) := by
  unfold depDecls
  exact if_pos rfl

def depTs : List (Tm Head 2) := [.var 1, .var 0]

theorem dep_listSub :
    (listSub 1 depTs (0 : Fin 1) : Tm Head 2) = .var (1 : Fin 2) := by
  unfold listSub depTs
  rfl

theorem dep_argType :
    (argType depEntry depTs 1 : CTm Head 2) = .var (1 : Fin 2) := by
  simp only [argType, argSub, depEntry, liftTm, CTm.annotateWith, CTm.subst, dep_listSub]

theorem dep_fo : ∀ t ∈ (depTs : List (Tm Head 2)), firstOrder t = true := by
  intro t ht
  obtain rfl | ht := List.mem_cons.mp ht
  · simp only [firstOrder]
  · cases List.mem_singleton.mp ht
    simp only [firstOrder]

theorem fin2_one_ne_zero : (1 : Fin 2) ≠ 0 := by
  intro h
  exact Nat.zero_ne_one (congrArg Fin.val h).symm

theorem dep_alone (j' : Nat) (t' : Tm Head 2) (hne : j' ≠ 1) (ht : depTs[j']? = some t') :
    AlgebraicSchema.variableMultiplicity (0 : Fin 2) t' = 0 := by
  have hlt := lt_of_getElem?_some ht
  cases j' with
  | zero =>
      simp only [depTs, List.getElem?_cons_zero] at ht
      cases ht
      exact variableMultiplicity_var_ne fin2_one_ne_zero
  | succ j' =>
      cases j' with
      | zero => exact absurd rfl hne
      | succ k =>
          simp only [depTs, List.length_cons, List.length_nil] at hlt
          exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt)) (Nat.not_lt_zero k)

/-- The second metavariable is known at the second entry, with the first
metavariable substituted for variable `0`. -/
theorem dep_second (expected : Option (CTm Head 2)) :
    patternKnowledge depDecls expected (Normalization.appSpine (.const depF) depTs) (0 : Fin 2) =
      some (.var (1 : Fin 2)) := by
  have hlen : (depTs : List (Tm Head 2)).length ≤ 2 := by
    simp only [depTs, List.length_cons, List.length_nil]
    exact Nat.le_refl 2
  have ht : (depTs : List (Tm Head 2))[1]? = some (.var (0 : Fin 2)) := by
    simp only [depTs]
    rfl
  rw [spine_knowledge_var depDecls depF 2 depEntry depC depDeclared depTs dep_fo hlen 1
      (0 : Fin 2) ht dep_alone expected, dep_argType]

end Dependent

section Iota

def iotaEntry : (j : Nat) → Tm Head j
  | 0 => .const (Lean.Name.mkSimple "motiveType")
  | 1 => .var 0
  | 2 => .const (Lean.Name.mkSimple "T")
  | _ + 3 => .const (Lean.Name.mkSimple "T")

def iotaC : Tm Head 3 := .const (Lean.Name.mkSimple "result")

def iotaSpine (k : DeclName) : List (Tm Head 3) :=
  [.var 2, .var 1, .app (.const k) (.var 0)]

def iotaDecls (rec c : DeclName) : Option (CTm Head 0) :=
  if c = rec then some (liftTm (closeType (Normalization.ofEntries iotaEntry 3) iotaC)) else none

theorem iotaDeclared (rec : DeclName) :
    (iotaDecls rec rec : Option (CTm Head 0)) =
      some (liftTm (closeType (Normalization.ofEntries iotaEntry 3) iotaC)) := by
  unfold iotaDecls
  exact if_pos rfl

theorem metaVars_three : metaVars (Head := Head) 3 =
    [.var (2 : Fin 3), .var 1, .var 0] := by
  simp only [metaVars, List.finRange_succ, List.finRange_zero, List.map_nil, List.map_cons,
    List.map_append, List.reverse_nil, List.reverse_cons, List.nil_append,
    List.singleton_append, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rfl

theorem iotaLeft_shape (rec k : DeclName) :
    (iotaLeft rec k 1 1 : Tm Head (1 + 1 + 1)) =
      Normalization.appSpine (.const rec) (iotaSpine k) := by
  rw [iotaLeft, Normalization.recApp, metaVars_three]
  rfl

theorem iota_fo (k : DeclName) :
    ∀ t ∈ (iotaSpine k : List (Tm Head 3)), firstOrder t = true := by
  intro t ht
  obtain rfl | ht := List.mem_cons.mp ht
  · simp only [firstOrder]
  · obtain rfl | ht := List.mem_cons.mp ht
    · simp only [firstOrder]
    · cases List.mem_singleton.mp ht
      simp only [firstOrder]
      rfl

theorem fin3_one_ne_two : (1 : Fin 3) ≠ 2 := by
  intro h
  exact Nat.zero_ne_one (Nat.succ.inj (congrArg Fin.val h))

theorem fin3_two_ne_one : (2 : Fin 3) ≠ 1 := by
  intro h
  exact Nat.zero_ne_one (Nat.succ.inj (congrArg Fin.val h)).symm

theorem fin3_zero_ne_one : (0 : Fin 3) ≠ 1 := by
  intro h
  exact Nat.zero_ne_one (congrArg Fin.val h)

theorem fin3_zero_ne_two : (0 : Fin 3) ≠ 2 := by
  intro h
  exact Nat.succ_ne_zero 1 (congrArg Fin.val h).symm

theorem iota_alone (k : DeclName) (j : Nat) (v : Fin 3)
    (h0 : j ≠ 0 →
      AlgebraicSchema.variableMultiplicity v (.var (2 : Fin 3) : Tm Head 3) = 0)
    (h1 : j ≠ 1 →
      AlgebraicSchema.variableMultiplicity v (.var (1 : Fin 3) : Tm Head 3) = 0)
    (h2 : j ≠ 2 →
      AlgebraicSchema.variableMultiplicity v
        (.app (.const k) (.var (0 : Fin 3)) : Tm Head 3) = 0)
    (j' : Nat) (t' : Tm Head 3) (hne : j' ≠ j) (ht : (iotaSpine k)[j']? = some t') :
    AlgebraicSchema.variableMultiplicity v t' = 0 := by
  have hlt := lt_of_getElem?_some ht
  cases hdec0 : decide (j' = 0) with
  | true =>
      have hj' : j' = 0 := of_decide_eq_true hdec0
      subst hj'
      simp only [iotaSpine, List.getElem?_cons_zero] at ht
      cases ht
      exact h0 hne.symm
  | false =>
      have hj0 : j' ≠ 0 := of_decide_eq_false hdec0
      cases hdec1 : decide (j' = 1) with
      | true =>
          have hj' : j' = 1 := of_decide_eq_true hdec1
          subst hj'
          simp only [iotaSpine, List.getElem?_cons_succ, List.getElem?_cons_zero] at ht
          cases ht
          exact h1 hne.symm
      | false =>
          have hlen : ((iotaSpine k) : List (Tm Head 3)).length = 3 := rfl
          rw [hlen] at hlt
          have hj' : j' = 2 := by
            cases j' with
            | zero => exact absurd rfl hj0
            | succ j' =>
                cases j' with
                | zero => exact absurd rfl (of_decide_eq_false hdec1)
                | succ j' =>
                    cases j' with
                    | zero => rfl
                    | succ n =>
                        exact False.elim (Nat.lt_irrefl 3
                          (Nat.lt_of_le_of_lt (Nat.le_add_left 3 n) hlt))
          subst hj'
          simp only [iotaSpine, List.getElem?_cons_succ, List.getElem?_cons_zero] at ht
          cases ht
          exact h2 hne.symm

theorem iota_method_domain :
    (argType iotaEntry [.var (2 : Fin 3)] 1 : CTm Head 3) = .var (2 : Fin 3) := by
  simp only [argType, argSub, iotaEntry, liftTm, CTm.annotateWith, CTm.subst, listSub]
  rfl

theorem iota_full_method_domain (k : DeclName) :
    (argType iotaEntry (iotaSpine k) 1 : CTm Head 3) = .var (2 : Fin 3) := by
  simp only [argType, argSub, iotaEntry, iotaSpine, liftTm, CTm.annotateWith, CTm.subst, listSub]
  rfl

theorem iota_motive_domain (k : DeclName) :
    (argType iotaEntry (iotaSpine k) 0 : CTm Head 3) =
      .const (Lean.Name.mkSimple "motiveType") := by
  simp only [argType, iotaEntry, liftTm, CTm.annotateWith, CTm.subst]

/-- After the motive, the spine synthesizes a dependent function whose domain is
the motive metavariable, the method entry with that metavariable substituted.
The codomain is the remaining type at the next entry. -/
theorem iota_after_motive (rec : DeclName) :
    ∃ (B : CTm Head (3 + 1)) (R : Tm Head 2), Remaining iotaEntry 3 iotaC 2 R ∧
      (elaborate (iotaDecls rec) Knowledge.empty none none
        (Normalization.appSpine (.const rec) [.var (2 : Fin 3)])).2 =
        some (.pi (.var (2 : Fin 3)) B) ∧
      B = (liftTm R).subst (CTm.liftSub (argSub [.var (2 : Fin 3)] 1)) := by
  have fo : ∀ t ∈ ([.var (2 : Fin 3)] : List (Tm Head 3)), firstOrder t = true := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    simp only [firstOrder]
  obtain ⟨B, hB, R, hR, hcod⟩ := spine_synthesizes (iotaDecls rec) rec 3 iotaEntry iotaC
    (iotaDeclared rec) [.var (2 : Fin 3)] fo (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
  refine ⟨B, R, hR, ?_, hcod⟩
  rw [List.length_singleton] at hB
  rw [hB, iota_method_domain]

/-- The motive metavariable is known at the motive entry. -/
theorem iota_motive (rec k : DeclName) (expected : Option (CTm Head 3)) :
    patternKnowledge (iotaDecls rec) expected (iotaLeft rec k 1 1) (2 : Fin 3) =
      some (.const (Lean.Name.mkSimple "motiveType")) := by
  rw [iotaLeft_shape]
  have hlen : ((iotaSpine k) : List (Tm Head 3)).length ≤ 3 := by
    simp only [iotaSpine, List.length_cons, List.length_nil]
    exact Nat.le_refl 3
  have ht : ((iotaSpine k) : List (Tm Head 3))[0]? = some (.var (2 : Fin 3)) := by
    simp only [iotaSpine]
    rfl
  have alone := iota_alone (Head := Head) k 0 (2 : Fin 3)
    (fun h => absurd rfl h)
    (fun _ => variableMultiplicity_var_ne (Head := Head) fin3_one_ne_two)
    (fun _ => variableMultiplicity_app_const_var (Head := Head) k fin3_zero_ne_two)
  rw [spine_knowledge_var (iotaDecls rec) rec 3 iotaEntry iotaC (iotaDeclared rec)
      (iotaSpine k) (iota_fo k) hlen 0 (2 : Fin 3) ht alone expected,
    iota_motive_domain]

/-- A method metavariable is known at the method entry with the motive substituted. -/
theorem iota_method (rec k : DeclName) (expected : Option (CTm Head 3)) :
    patternKnowledge (iotaDecls rec) expected (iotaLeft rec k 1 1) (1 : Fin 3) =
      some (.var (2 : Fin 3)) := by
  rw [iotaLeft_shape]
  have hlen : ((iotaSpine k) : List (Tm Head 3)).length ≤ 3 := by
    simp only [iotaSpine, List.length_cons, List.length_nil]
    exact Nat.le_refl 3
  have ht : ((iotaSpine k) : List (Tm Head 3))[1]? = some (.var (1 : Fin 3)) := by
    simp only [iotaSpine]
    rfl
  have alone := iota_alone (Head := Head) k 1 (1 : Fin 3)
    (fun _ => variableMultiplicity_var_ne (Head := Head) fin3_two_ne_one)
    (fun h => absurd rfl h)
    (fun _ => variableMultiplicity_app_const_var (Head := Head) k fin3_zero_ne_one)
  rw [spine_knowledge_var (iotaDecls rec) rec 3 iotaEntry iotaC (iotaDeclared rec)
      (iotaSpine k) (iota_fo k) hlen 1 (1 : Fin 3) ht alone expected,
    iota_full_method_domain]

end Iota

section Repeated

def negEntry : (j : Nat) → Tm Head j
  | 0 => .const (Lean.Name.mkSimple "left")
  | 1 => .const (Lean.Name.mkSimple "right")
  | _ + 2 => .const (Lean.Name.mkSimple "right")

def negC : Tm Head 2 := .const (Lean.Name.mkSimple "C")

def negF : DeclName := Lean.Name.mkSimple "f"

def negDecls (c : DeclName) : Option (CTm Head 0) :=
  if c = negF then some (liftTm (closeType (Normalization.ofEntries negEntry 2) negC)) else none

theorem negDeclared :
    (negDecls negF : Option (CTm Head 0)) =
      some (liftTm (closeType (Normalization.ofEntries negEntry 2) negC)) := by
  unfold negDecls
  exact if_pos rfl

def negTs : List (Tm Head 1) := [.var 0, .var 0]

def negPrefix : List (Tm Head 1) := [.var 0]

theorem neg_arg_left :
    (argType negEntry negPrefix 0 : CTm Head 1) = .const (Lean.Name.mkSimple "left") := by
  simp only [argType, negEntry, liftTm, CTm.annotateWith, CTm.subst]

theorem neg_arg_right :
    (argType negEntry negTs 1 : CTm Head 1) = .const (Lean.Name.mkSimple "right") := by
  simp only [argType, negEntry, liftTm, CTm.annotateWith, CTm.subst]

theorem neg_prefix_fo :
    ∀ t ∈ (negPrefix : List (Tm Head 1)), firstOrder t = true := by
  intro t ht
  cases List.mem_singleton.mp ht
  simp only [firstOrder]

theorem neg_prefix_alone (j' : Nat) (t' : Tm Head 1) (hne : j' ≠ 0)
    (ht : negPrefix[j']? = some t') :
    AlgebraicSchema.variableMultiplicity (0 : Fin 1) t' = 0 := by
  have hlt := lt_of_getElem?_some ht
  exact absurd (Nat.lt_one_iff.mp hlt) hne

theorem neg_const_ne :
    (.const (Lean.Name.mkSimple "left") : CTm Head 1) ≠ .const (Lean.Name.mkSimple "right") := by
  intro h
  injection h with _ hn
  unfold Lean.Name.mkSimple at hn
  injection hn with _ hs
  exact absurd hs (by decide)

/-- The repeated metavariable is known at the first entry. The one-argument
prefix satisfies the absence condition, and the merge keeps that `some`. -/
theorem neg_knowledge (expected : Option (CTm Head 1)) :
    patternKnowledge negDecls expected (Normalization.appSpine (.const negF) negTs) (0 : Fin 1) =
      some (.const (Lean.Name.mkSimple "left")) := by
  have hlen : (negPrefix : List (Tm Head 1)).length ≤ 2 := by
    simp only [negPrefix, List.length_cons, List.length_nil]
    exact Nat.le_succ 1
  have ht : (negPrefix : List (Tm Head 1))[0]? = some (.var (0 : Fin 1)) := by
    simp only [negPrefix]
    rfl
  have hprefix := spine_knowledge_var negDecls negF 2 negEntry negC negDeclared negPrefix
    neg_prefix_fo hlen 0 (0 : Fin 1) ht neg_prefix_alone expected
  have hsame := patternKnowledge_spine_expected negDecls negF negPrefix none expected (0 : Fin 1)
  rw [show negTs = negPrefix ++ [.var (0 : Fin 1)] by rfl,
    Normalization.appSpine_concat, patternKnowledge_app,
    merge_left_of_some (hsame.trans hprefix), neg_arg_left]

/-- At the second copy the absence condition fails, and the knowledge is not the
second entry. Item 3's equation for that position is false. -/
theorem neg_second_fails (expected : Option (CTm Head 1)) :
    patternKnowledge negDecls expected (Normalization.appSpine (.const negF) negTs) (0 : Fin 1) ≠
      patternKnowledge negDecls (some (argType negEntry negTs 1)) (.var (0 : Fin 1))
        (0 : Fin 1) := by
  intro h
  rw [neg_knowledge expected, neg_arg_right] at h
  simp only [patternKnowledge] at h
  injection h with h
  exact neg_const_ne h

end Repeated

#print axioms patternKnowledge_absent
#print axioms spine_synthesizes
#print axioms spine_knowledge

end SpineExamples

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
