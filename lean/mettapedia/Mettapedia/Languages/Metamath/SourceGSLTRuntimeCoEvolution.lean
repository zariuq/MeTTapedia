import Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement

/-!
# Runtime co-evolution: the shipped operations preserve agreement

`SourceGSLTRuntimeStateAgreement` states the complete source/runtime
agreement and proves it for scope push/pop/completion; insertion and
scope-pop carried a post-projection premise.  This module discharges
that premise constructively: the canonical checker view evolves under
the real shipped hash-map operations exactly as the source declaration
state evolves, so agreement is preserved across every declaration
transition with no supplied projection.  For a `$p`, this layer models
only the assertion insertion that follows a successful proof: it does not
execute or validate the proof.  That separate obligation is carried by
`TheoremObligation` and discharged by the lifecycle correspondence.

The keystone is the canonical-order representation theorem: inserting
a fresh label into the runtime object map splits the label-sorted
entry list at the insertion point, with everything else unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
open Metamath.Verify

/-- The record update backing every shipped fresh insertion. -/
def insertObj (db : RuntimeDB) (l : String)
    (obj : Metamath.Verify.Object) : RuntimeDB :=
  { db with objects := db.objects.insert l obj }

/-! ## Sorted-list algebra -/

private theorem eq_of_perm_of_pairwise_lt {α : Type _}
    {r : α → α → Prop} (hasymm : ∀ a b, r a b → r b a → False) :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise r →
      l₂.Pairwise r → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ hperm _ _
      exact (hperm.nil_eq).symm ▸ rfl
  | cons a t₁ ih =>
      intro l₂ hperm h₁ h₂
      cases l₂ with
      | nil => exact absurd hperm.symm.nil_eq (by simp)
      | cons b t₂ =>
          by_cases hab : a = b
          · subst hab
            have htails := hperm.cons_inv
            rw [ih htails (List.Pairwise.of_cons h₁)
              (List.Pairwise.of_cons h₂)]
          · exfalso
            have haIn : a ∈ b :: t₂ := hperm.mem_iff.mp (by simp)
            have hbIn : b ∈ a :: t₁ := hperm.symm.mem_iff.mp (by simp)
            have hat₂ : a ∈ t₂ := by
              rcases List.mem_cons.mp haIn with heq | h
              · exact absurd heq hab
              · exact h
            have hbt₁ : b ∈ t₁ := by
              rcases List.mem_cons.mp hbIn with heq | h
              · exact absurd heq.symm hab
              · exact h
            have hrab : r a b := (List.pairwise_cons.mp h₁).1 b hbt₁
            have hrba : r b a := (List.pairwise_cons.mp h₂).1 a hat₂
            exact hasymm a b hrab hrba

/-- Label-sorted entry lists of key-distinct permutations coincide. -/
theorem sortObjectEntries_eq_of_perm
    {l₁ l₂ : List (String × Metamath.Verify.Object)}
    (hperm : l₁.Perm l₂)
    (hnodup : l₁.Pairwise (fun a b => a.1 ≠ b.1)) :
    sortObjectEntries l₁ = sortObjectEntries l₂ := by
  have htrans : ∀ (a b c : String × Metamath.Verify.Object),
      (decide (a.1 ≤ b.1)) → (decide (b.1 ≤ c.1)) →
        (decide (a.1 ≤ c.1) : Bool) := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    exact le_trans hab hbc
  have htotal : ∀ (a b : String × Metamath.Verify.Object),
      (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1) : Bool) := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total a.1 b.1
  have hs₁ := List.pairwise_mergeSort htrans htotal l₁
  have hs₂ := List.pairwise_mergeSort htrans htotal l₂
  have hp₁ := List.mergeSort_perm l₁ (fun a b => a.1 ≤ b.1)
  have hp₂ := List.mergeSort_perm l₂ (fun a b => a.1 ≤ b.1)
  have hnodup₁ :
      (sortObjectEntries l₁).Pairwise (fun a b => a.1 ≠ b.1) :=
    (hp₁.pairwise_iff (fun h heq => h heq.symm)).mpr hnodup
  have hnodup₂ :
      (sortObjectEntries l₂).Pairwise (fun a b => a.1 ≠ b.1) :=
    (hp₂.pairwise_iff (fun h heq => h heq.symm)).mpr
      ((hperm.pairwise_iff (fun h heq => h heq.symm)).mp hnodup)
  have hlt₁ : (sortObjectEntries l₁).Pairwise
      (fun a b => a.1 < b.1) := by
    have := hs₁.and hnodup₁
    exact this.imp (fun ⟨hle, hne⟩ =>
      lt_of_le_of_ne (by simpa using hle) hne)
  have hlt₂ : (sortObjectEntries l₂).Pairwise
      (fun a b => a.1 < b.1) := by
    have := hs₂.and hnodup₂
    exact this.imp (fun ⟨hle, hne⟩ =>
      lt_of_le_of_ne (by simpa using hle) hne)
  have hperm' : (sortObjectEntries l₁).Perm (sortObjectEntries l₂) :=
    (hp₁.trans hperm).trans hp₂.symm
  exact eq_of_perm_of_pairwise_lt
    (fun a b hab hba => absurd (lt_trans hab hba) (lt_irrefl _))
    hperm' hlt₁ hlt₂

/-- Fresh keys never occur among the entries. -/
private theorem key_ne_of_fresh {db : RuntimeDB} {l : String}
    (hfresh : db.find? l = none) :
    ∀ e ∈ db.objects.toList, l ≠ e.1 := by
  intro e he heq
  have hkey : db.objects[e.1]? = some e.2 :=
    (Std.HashMap.mem_toList_iff_getElem?_eq_some).mp (by simpa using he)
  rw [← heq] at hkey
  rw [show db.objects[l]? = db.find? l from rfl, hfresh] at hkey
  exact nomatch hkey

/-- **Canonical-order representation**: inserting a fresh label splits
the sorted entry list at its ordered position; every prior entry keeps
its position and content. -/
theorem objectEntries_insert_fresh {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none) :
    ∃ pre post,
      objectEntries db = pre ++ post ∧
        objectEntries (insertObj db l obj) =
          pre ++ (l, obj) :: post ∧
        ∀ e ∈ pre, ¬((l, obj).1 ≤ e.1) := by
  have hnodupBeq := Std.HashMap.distinct_keys_toList (m := db.objects)
  have hnodup : db.objects.toList.Pairwise (fun a b => a.1 ≠ b.1) :=
    hnodupBeq.imp (fun h => by simpa using h)
  have hperm :
      (db.objects.insert l obj).toList.Perm
        ((l, obj) :: db.objects.toList) := by
    have hstep := Std.HashMap.toList_insert_perm
      (m := db.objects) (k := l) (v := obj)
    have hfilter : db.objects.toList.filter
        (fun x => !decide (l = x.1)) = db.objects.toList := by
      apply List.filter_eq_self.mpr
      intro e he
      have := key_ne_of_fresh hfresh e he
      simp [this]
    simpa [hfilter] using hstep
  have hnodup' :
      ((l, obj) :: db.objects.toList).Pairwise
        (fun a b => a.1 ≠ b.1) := by
    refine List.Pairwise.cons ?_ hnodup
    intro e he
    exact key_ne_of_fresh hfresh e he
  have htrans : ∀ (a b c : String × Metamath.Verify.Object),
      (decide (a.1 ≤ b.1)) → (decide (b.1 ≤ c.1)) →
        (decide (a.1 ≤ c.1) : Bool) := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    exact le_trans hab hbc
  have htotal : ∀ (a b : String × Metamath.Verify.Object),
      (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1) : Bool) := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total a.1 b.1
  obtain ⟨pre, post, hsplit₁, hsplit₂, hpre⟩ :=
    List.mergeSort_cons htrans htotal (l, obj) db.objects.toList
  refine ⟨pre, post, ?_, ?_, ?_⟩
  · exact hsplit₂ ▸ rfl
  · have : objectEntries (insertObj db l obj) =
        sortObjectEntries ((l, obj) :: db.objects.toList) := by
      exact sortObjectEntries_eq_of_perm hperm
        ((hperm.pairwise_iff (fun h heq => h heq.symm)).mpr hnodup')
    rw [this]
    exact hsplit₁
  · intro e he
    have := hpre e he
    simpa using this

/-! ## Lookup stability under fresh insertion -/

@[simp] theorem insertObj_frame (db : RuntimeDB) (l : String)
    (obj : Metamath.Verify.Object) :
    (insertObj db l obj).frame = db.frame := rfl

@[simp] theorem insertObj_scopes (db : RuntimeDB) (l : String)
    (obj : Metamath.Verify.Object) :
    (insertObj db l obj).scopes = db.scopes := rfl

@[simp] theorem insertObj_error (db : RuntimeDB) (l : String)
    (obj : Metamath.Verify.Object) :
    (insertObj db l obj).error? = db.error? := rfl

theorem find?_insertObj (db : RuntimeDB) (l : String)
    (obj : Metamath.Verify.Object) (l' : String) :
    (insertObj db l obj).find? l' =
      if l = l' then some obj else db.find? l' := by
  show (db.objects.insert l obj)[l']? = _
  rw [Std.HashMap.getElem?_insert]
  by_cases h : l = l' <;> simp [h, DB.find?]

theorem find?_insertObj_self (db : RuntimeDB) (l : String)
    (obj : Metamath.Verify.Object) :
    (insertObj db l obj).find? l = some obj := by
  rw [find?_insertObj]
  simp

theorem find?_insertObj_ne {db : RuntimeDB} {l l' : String}
    {obj : Metamath.Verify.Object} (hne : l ≠ l') :
    (insertObj db l obj).find? l' = db.find? l' := by
  rw [find?_insertObj]
  simp [hne]

/-- Occupied labels are never the fresh one. -/
theorem occupied_ne_fresh {db : RuntimeDB} {l l' : String}
    (hfresh : db.find? l = none) (hocc : db.find? l' ≠ none) :
    l ≠ l' := by
  intro heq
  rw [← heq] at hocc
  exact hocc hfresh

theorem find?_insertObj_occupied {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    {l' : String} (hocc : db.find? l' ≠ none) :
    (insertObj db l obj).find? l' = db.find? l' :=
  find?_insertObj_ne (occupied_ne_fresh hfresh hocc)

/-! ## Guard congruence under fresh insertion -/

theorem hypOK?_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    {label : String} (hOK : db.hypOK? label = true) :
    (insertObj db l obj).hypOK? label = true := by
  have hocc : db.find? label ≠ none := by
    intro hnone
    rw [DB.hypOK?, hnone] at hOK
    exact nomatch hOK
  rw [DB.hypOK?, find?_insertObj_occupied hfresh hocc]
  rw [DB.hypOK?] at hOK
  exact hOK

theorem frameHypsOk?_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    {fr : RuntimeFrame} (hOK : db.frameHypsOk? fr = true) :
    (insertObj db l obj).frameHypsOk? fr = true := by
  rw [DB.frameHypsOk?] at hOK ⊢
  rw [List.all_eq_true] at hOK ⊢
  intro i hi
  exact hypOK?_insertObj hfresh (hOK i hi)

theorem frameFloatVarsUnique?_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    {fr : RuntimeFrame} (hhyps : db.frameHypsOk? fr = true)
    (hOK : db.frameFloatVarsUnique? fr = true) :
    (insertObj db l obj).frameFloatVarsUnique? fr = true := by
  have hstable : ∀ i ∈ List.range fr.hyps.size,
      (insertObj db l obj).find? fr.hyps[i]! = db.find? fr.hyps[i]! := by
    intro i hi
    refine find?_insertObj_occupied hfresh ?_
    rw [DB.frameHypsOk?, List.all_eq_true] at hhyps
    have := hhyps i hi
    rw [DB.hypOK?] at this
    intro hnone
    rw [hnone] at this
    exact nomatch this
  rw [DB.frameFloatVarsUnique?] at hOK ⊢
  rw [List.all_eq_true] at hOK ⊢
  intro i hi
  rw [List.all_eq_true]
  have hOKi := hOK i hi
  rw [List.all_eq_true] at hOKi
  intro j hj
  have hOKij := hOKi j hj
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, dite_false] at hOKij ⊢
    rw [hstable i hi, hstable j hj]
    exact hOKij

theorem wellFormedFrame?_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    {fr : RuntimeFrame} (hOK : db.wellFormedFrame? fr = true) :
    (insertObj db l obj).wellFormedFrame? fr = true := by
  rw [DB.wellFormedFrame?, Bool.and_eq_true] at hOK ⊢
  exact ⟨frameHypsOk?_insertObj hfresh hOK.1,
    frameFloatVarsUnique?_insertObj hfresh hOK.1 hOK.2⟩

theorem wellFormedObj?_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    {lbl : String} {o : Metamath.Verify.Object}
    (hOK : db.wellFormedObj? lbl o = true) :
    (insertObj db l obj).wellFormedObj? lbl o = true := by
  cases o with
  | const c => exact hOK
  | var v => exact hOK
  | hyp ess f e => exact hOK
  | assert f fr e =>
      rw [DB.wellFormedObj?, Bool.and_eq_true] at hOK ⊢
      exact ⟨hOK.1, wellFormedFrame?_insertObj hfresh hOK.2⟩

theorem frameFloatVars_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    {fr : RuntimeFrame}
    (hres : ∀ lbl ∈ fr.hyps.toList, db.find? lbl ≠ none) :
    (insertObj db l obj).frameFloatVars fr = db.frameFloatVars fr := by
  rw [DB.frameFloatVars, DB.frameFloatVars]
  apply List.filterMap_congr
  intro lbl hlbl
  rw [find?_insertObj_occupied hfresh (hres lbl hlbl)]

theorem frameDvVarsInFrame?_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    {fr : RuntimeFrame}
    (hres : ∀ lbl ∈ fr.hyps.toList, db.find? lbl ≠ none)
    (hOK : db.frameDvVarsInFrame? fr = true) :
    (insertObj db l obj).frameDvVarsInFrame? fr = true := by
  rw [DB.frameDvVarsInFrame?] at hOK ⊢
  rw [frameFloatVars_insertObj hfresh hres]
  exact hOK

/-! ## Whole-map guards under fresh insertion -/

/-- The insert-perm, standalone. -/
theorem toList_insertObj_perm {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none) :
    (insertObj db l obj).objects.toList.Perm
      ((l, obj) :: db.objects.toList) := by
  show (db.objects.insert l obj).toList.Perm _
  have hstep := Std.HashMap.toList_insert_perm
    (m := db.objects) (k := l) (v := obj)
  have hfilter : db.objects.toList.filter
      (fun x => !decide (l = x.1)) = db.objects.toList := by
    apply List.filter_eq_self.mpr
    intro e he
    have := key_ne_of_fresh hfresh e he
    simp [this]
  simpa [hfilter] using hstep

theorem resolve_of_frameHypsOk {db : RuntimeDB} {fr : RuntimeFrame}
    (h : db.frameHypsOk? fr = true) :
    ∀ lbl ∈ fr.hyps.toList, db.find? lbl ≠ none := by
  intro lbl hlbl
  obtain ⟨i, hlt, hEq⟩ := List.mem_iff_getElem.mp hlbl
  rw [DB.frameHypsOk?, List.all_eq_true] at h
  have hi : i ∈ List.range fr.hyps.size := by
    rw [List.mem_range]
    simpa using hlt
  have hOK := h i hi
  rw [DB.hypOK?] at hOK
  have hbang : fr.hyps[i]! = lbl := by
    rw [getElem!_pos fr.hyps i (by simpa using hlt)]
    rw [← hEq]
    simp
  rw [hbang] at hOK
  intro hnone
  rw [hnone] at hOK
  exact nomatch hOK

theorem wellFormedObjects?_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    (hOK : db.wellFormedObjects? = true)
    (hnew : (insertObj db l obj).wellFormedObj? l obj = true) :
    (insertObj db l obj).wellFormedObjects? = true := by
  rw [DB.wellFormedObjects?, List.all_eq_true]
  intro kv hkv
  have hkv' := (toList_insertObj_perm hfresh).mem_iff.mp hkv
  rcases List.mem_cons.mp hkv' with rfl | hold
  · exact hnew
  · rw [DB.wellFormedObjects?, List.all_eq_true] at hOK
    exact wellFormedObj?_insertObj hfresh (hOK kv hold)

theorem assertDvVarsInFrame?_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    (hwf : db.wellFormedObjects? = true)
    (hOK : db.assertDvVarsInFrame? = true)
    (hnew : match obj with
      | .assert _ fr _ =>
          (insertObj db l obj).frameDvVarsInFrame? fr = true
      | _ => True) :
    (insertObj db l obj).assertDvVarsInFrame? = true := by
  rw [DB.assertDvVarsInFrame?, List.all_eq_true]
  intro kv hkv
  have hkv' := (toList_insertObj_perm hfresh).mem_iff.mp hkv
  rcases List.mem_cons.mp hkv' with rfl | hold
  · cases obj with
    | assert f fr e => exact hnew
    | const c => trivial
    | var v => trivial
    | hyp ess f e => trivial
  · cases hkvo : kv.2 with
    | assert f fr e =>
        rw [DB.assertDvVarsInFrame?, List.all_eq_true] at hOK
        have hOKkv := hOK kv hold
        rw [hkvo] at hOKkv
        rw [DB.wellFormedObjects?, List.all_eq_true] at hwf
        have hwfkv := hwf kv hold
        rw [hkvo, DB.wellFormedObj?, Bool.and_eq_true] at hwfkv
        have hres := resolve_of_frameHypsOk (by
          rw [DB.wellFormedFrame?, Bool.and_eq_true] at hwfkv
          exact hwfkv.2.1)
        exact frameDvVarsInFrame?_insertObj hfresh hres hOKkv
    | const c => trivial
    | var v => trivial
    | hyp ess f e => trivial

theorem wellFormed?_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    (hOK : db.wellFormed? = true)
    (hnew : (insertObj db l obj).wellFormedObj? l obj = true) :
    (insertObj db l obj).wellFormed? = true := by
  rw [DB.wellFormed?, Bool.and_eq_true] at hOK ⊢
  exact ⟨wellFormedFrame?_insertObj hfresh hOK.1,
    wellFormedObjects?_insertObj hfresh hOK.2 hnew⟩

theorem rawCallerDVStrict_insertObj (db : RuntimeDB) (l : String)
    (obj : Metamath.Verify.Object) :
    rawCallerDVStrict (insertObj db l obj) = rawCallerDVStrict db := rfl

/-! ## Inverting and rebuilding the shared projector -/

private theorem guard_bind_some {c : Prop} [Decidable c] {α : Type _}
    {rest : Option α} {a : α}
    (h : (do guard c; rest) = some a) : c ∧ rest = some a := by
  by_cases hc : c
  · refine ⟨hc, ?_⟩
    simpa [guard, hc] using h
  · simp [guard, hc] at h

private theorem bind_some_inv {α β : Type _} {o : Option β}
    {f : β → Option α} {a : α}
    (h : (o >>= f) = some a) : ∃ b, o = some b ∧ f b = some a := by
  cases ho : o with
  | none => rw [ho] at h; exact nomatch h
  | some b => rw [ho] at h; exact ⟨b, rfl, h⟩

/-- Full inversion of a successful shared projection. -/
theorem projectPrefix?_ok_inv {db : RuntimeDB}
    {proj : PrefixProjection} (h : projectPrefix? db = some proj) :
    db.error?.isNone = true ∧ db.wellFormed? = true ∧
      db.assertDvVarsInFrame? = true ∧ rawCallerDVStrict db = true ∧
      ((objectEntries db).all fun e =>
        objectEmbeddedNameMatches e.1 e.2) = true ∧
      ((declaredConstantNames (objectEntries db)).all fun c =>
        !((declaredVariableNames (objectEntries db)).contains c)) =
          true ∧
      ∃ hyps,
        projectHypotheses? db db.frame.hyps.toList = some hyps ∧
          frameProjectionValid (proofFacingCallerFrame db) hyps =
            true ∧
          ∃ asserts,
            projectAssertionsFromEntries? db (objectEntries db) =
              some asserts ∧
              prefixProjectionValid proj = true ∧
              proj =
                { declaredConstants :=
                    declaredConstantNames (objectEntries db),
                  declaredVariables :=
                    declaredVariableNames (objectEntries db),
                  callerFrame := proofFacingCallerFrame db,
                  activeHypotheses := hyps,
                  assertions := asserts } := by
  simp only [projectPrefix?] at h
  obtain ⟨h1, h⟩ := guard_bind_some h
  obtain ⟨h2, h⟩ := guard_bind_some h
  obtain ⟨h3, h⟩ := guard_bind_some h
  obtain ⟨h4, h⟩ := guard_bind_some h
  obtain ⟨h5, h⟩ := guard_bind_some h
  obtain ⟨h6, h⟩ := guard_bind_some h
  obtain ⟨hyps, hhyps, h⟩ := bind_some_inv h
  obtain ⟨h7, h⟩ := guard_bind_some h
  obtain ⟨asserts, hasserts, h⟩ := bind_some_inv h
  obtain ⟨h8, h⟩ := guard_bind_some h
  have hproj := Option.some.inj h
  refine ⟨by simpa using h1, by simpa using h2, by simpa using h3,
    by simpa using h4, by simpa using h5, by simpa using h6,
    hyps, hhyps, by simpa using h7, asserts, hasserts, ?_, hproj.symm⟩
  rw [← hproj]
  simpa using h8

/-- Rebuild a successful shared projection from its components. -/
theorem projectPrefix?_eq_some_of {db : RuntimeDB}
    {hyps : List HypothesisView} {asserts : List AssertionView}
    (h1 : db.error?.isNone = true) (h2 : db.wellFormed? = true)
    (h3 : db.assertDvVarsInFrame? = true)
    (h4 : rawCallerDVStrict db = true)
    (h5 : ((objectEntries db).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true)
    (h6 : ((declaredConstantNames (objectEntries db)).all fun c =>
      !((declaredVariableNames (objectEntries db)).contains c)) = true)
    (hhyps : projectHypotheses? db db.frame.hyps.toList = some hyps)
    (h7 : frameProjectionValid (proofFacingCallerFrame db) hyps = true)
    (hasserts : projectAssertionsFromEntries? db (objectEntries db) =
      some asserts)
    (h8 : prefixProjectionValid
      { declaredConstants := declaredConstantNames (objectEntries db)
        declaredVariables := declaredVariableNames (objectEntries db)
        callerFrame := proofFacingCallerFrame db
        activeHypotheses := hyps
        assertions := asserts } = true) :
    projectPrefix? db = some
      { declaredConstants := declaredConstantNames (objectEntries db)
        declaredVariables := declaredVariableNames (objectEntries db)
        callerFrame := proofFacingCallerFrame db
        activeHypotheses := hyps
        assertions := asserts } := by
  simp [projectPrefix?, h1, h2, h3, h4, h5, hhyps, h7,
    hasserts, h8, guard]
  simpa using h6

/-! ## Hypothesis-projection stability -/

theorem projectHypothesis?_congr {db db' : RuntimeDB} {lbl : String}
    (hfind : db'.find? lbl = db.find? lbl) :
    projectHypothesis? db' lbl = projectHypothesis? db lbl := by
  unfold projectHypothesis?
  rw [hfind]

theorem projectHypothesis?_resolves {db : RuntimeDB} {lbl : String}
    {view : HypothesisView}
    (h : projectHypothesis? db lbl = some view) :
    db.find? lbl ≠ none := by
  unfold projectHypothesis? at h
  obtain ⟨obj, hobj, -⟩ := bind_some_inv h
  intro hnone
  rw [hnone] at hobj
  exact nomatch hobj

theorem projectHypotheses?_congr {db db' : RuntimeDB} :
    ∀ {labels : List String},
      (∀ lbl ∈ labels, db'.find? lbl = db.find? lbl) →
      projectHypotheses? db' labels = projectHypotheses? db labels := by
  intro labels
  induction labels with
  | nil => intro _; rfl
  | cons lbl rest ih =>
      intro hfind
      unfold projectHypotheses? at ih ⊢
      rw [List.mapM_cons, List.mapM_cons,
        projectHypothesis?_congr (hfind lbl (by simp)),
        ih (fun x hx => hfind x (by simp [hx]))]

theorem projectHypotheses?_resolves {db : RuntimeDB} :
    ∀ {labels : List String} {views : List HypothesisView},
      projectHypotheses? db labels = some views →
      ∀ lbl ∈ labels, db.find? lbl ≠ none := by
  intro labels
  induction labels with
  | nil => intro views _ lbl hlbl; exact absurd hlbl List.not_mem_nil
  | cons l rest ih =>
      intro views h lbl hlbl
      unfold projectHypotheses? at h
      rw [List.mapM_cons] at h
      obtain ⟨v, hv, h⟩ := bind_some_inv h
      obtain ⟨vs, hvs, -⟩ := bind_some_inv h
      rcases List.mem_cons.mp hlbl with rfl | htail
      · exact projectHypothesis?_resolves hv
      · exact ih hvs lbl htail

theorem projectHypotheses?_pointwise {db : RuntimeDB}
    {viewOf : String → HypothesisView} :
    ∀ {labels : List String},
      (∀ lbl ∈ labels, projectHypothesis? db lbl = some (viewOf lbl)) →
      projectHypotheses? db labels = some (labels.map viewOf) := by
  intro labels
  induction labels with
  | nil => intro _; rfl
  | cons l rest ih =>
      intro h
      unfold projectHypotheses? at ih ⊢
      rw [List.mapM_cons, h l (by simp),
        ih (fun x hx => h x (by simp [hx]))]
      rfl

/-! ## Assertion-collector stability and splitting -/

theorem projectAssertion?_congr {db db' : RuntimeDB} {label : String}
    {f : Metamath.Verify.Formula} {fr : RuntimeFrame} {e : String}
    (hfind : ∀ lbl ∈ fr.hyps.toList, db'.find? lbl = db.find? lbl) :
    projectAssertion? db' label f fr e =
      projectAssertion? db label f fr e := by
  unfold projectAssertion?
  rw [projectHypotheses?_congr hfind]

theorem projectAssertion?_resolves {db : RuntimeDB} {label : String}
    {f : Metamath.Verify.Formula} {fr : RuntimeFrame} {e : String}
    {view : AssertionView}
    (h : projectAssertion? db label f fr e = some view) :
    ∀ lbl ∈ fr.hyps.toList, db.find? lbl ≠ none := by
  unfold projectAssertion? at h
  obtain ⟨-, h⟩ := guard_bind_some h
  obtain ⟨formula, -, h⟩ := bind_some_inv h
  obtain ⟨hyps, hhyps, -⟩ := bind_some_inv h
  exact projectHypotheses?_resolves hhyps

theorem projectAssertionsFromEntries?_congr {db db' : RuntimeDB} :
    ∀ {entries : List (String × Metamath.Verify.Object)}
      {views : List AssertionView},
      projectAssertionsFromEntries? db entries = some views →
      (∀ e ∈ entries, ∀ (f : Metamath.Verify.Formula)
        (fr : RuntimeFrame) (emb : String), e.2 = .assert f fr emb →
        ∀ lbl ∈ fr.hyps.toList, db'.find? lbl = db.find? lbl) →
      projectAssertionsFromEntries? db' entries = some views := by
  intro entries
  induction entries with
  | nil =>
      intro views h _
      exact h
  | cons entry rest ih =>
      intro views h hfind
      obtain ⟨label, obj⟩ := entry
      cases obj with
      | assert f fr emb =>
          unfold projectAssertionsFromEntries? at h ⊢
          obtain ⟨view, hview, h⟩ := bind_some_inv h
          obtain ⟨others, hothers, h⟩ := bind_some_inv h
          rw [projectAssertion?_congr (db := db)
            (hfind (label, .assert f fr emb) (by simp) f fr emb rfl),
            hview]
          rw [ih hothers
            (fun e he f' fr' emb' hfr' =>
              hfind e (by simp [he]) f' fr' emb' hfr')]
          exact h
      | const c =>
          unfold projectAssertionsFromEntries? at h ⊢
          exact ih h
            (fun e he f' fr' emb' hfr' =>
              hfind e (by simp [he]) f' fr' emb' hfr')
      | var v =>
          unfold projectAssertionsFromEntries? at h ⊢
          exact ih h
            (fun e he f' fr' emb' hfr' =>
              hfind e (by simp [he]) f' fr' emb' hfr')
      | hyp ess f emb =>
          unfold projectAssertionsFromEntries? at h ⊢
          exact ih h
            (fun e he f' fr' emb' hfr' =>
              hfind e (by simp [he]) f' fr' emb' hfr')

theorem projectAssertionsFromEntries?_skip {db : RuntimeDB}
    {l : String} {obj : Metamath.Verify.Object}
    (hskip : ∀ (f : Metamath.Verify.Formula) (fr : RuntimeFrame)
      (emb : String), obj ≠ .assert f fr emb)
    {rest : List (String × Metamath.Verify.Object)} :
    projectAssertionsFromEntries? db ((l, obj) :: rest) =
      projectAssertionsFromEntries? db rest := by
  cases obj with
  | assert f fr emb => exact absurd rfl (hskip f fr emb)
  | const c => simp only [projectAssertionsFromEntries?]
  | var v => simp only [projectAssertionsFromEntries?]
  | hyp ess f emb => simp only [projectAssertionsFromEntries?]

theorem projectAssertionsFromEntries?_cons_assert {db : RuntimeDB}
    {l : String} {f : Metamath.Verify.Formula} {fr : RuntimeFrame}
    {emb : String} {view : AssertionView}
    {rest : List (String × Metamath.Verify.Object)}
    {vrest : List AssertionView}
    (hview : projectAssertion? db l f fr emb = some view)
    (hrest : projectAssertionsFromEntries? db rest = some vrest) :
    projectAssertionsFromEntries? db ((l, .assert f fr emb) :: rest) =
      some (view :: vrest) := by
  unfold projectAssertionsFromEntries?
  rw [hview, hrest]
  rfl

theorem projectAssertionsFromEntries?_cons_assert_inv {db : RuntimeDB}
    {l : String} {f : Metamath.Verify.Formula} {fr : RuntimeFrame}
    {emb : String}
    {rest : List (String × Metamath.Verify.Object)}
    {views : List AssertionView}
    (h : projectAssertionsFromEntries? db
      ((l, .assert f fr emb) :: rest) = some views) :
    ∃ view vrest,
      projectAssertion? db l f fr emb = some view ∧
        projectAssertionsFromEntries? db rest = some vrest ∧
        views = view :: vrest := by
  unfold projectAssertionsFromEntries? at h
  obtain ⟨view, hview, h⟩ := bind_some_inv h
  obtain ⟨vrest, hvrest, h⟩ := bind_some_inv h
  exact ⟨view, vrest, hview, hvrest, (Option.some.inj h).symm⟩

theorem projectAssertionsFromEntries?_append {db : RuntimeDB} :
    ∀ {pre post : List (String × Metamath.Verify.Object)}
      {vpre vpost : List AssertionView},
      projectAssertionsFromEntries? db pre = some vpre →
      projectAssertionsFromEntries? db post = some vpost →
      projectAssertionsFromEntries? db (pre ++ post) =
        some (vpre ++ vpost) := by
  intro pre
  induction pre with
  | nil =>
      intro post vpre vpost hpre hpost
      cases Option.some.inj hpre
      simpa using hpost
  | cons entry rest ih =>
      intro post vpre vpost hpre hpost
      obtain ⟨label, obj⟩ := entry
      cases obj with
      | assert f fr emb =>
          obtain ⟨view, vrest, hview, hvrest, rfl⟩ :=
            projectAssertionsFromEntries?_cons_assert_inv hpre
          rw [List.cons_append]
          exact projectAssertionsFromEntries?_cons_assert hview
            (ih hvrest hpost)
      | const c =>
          rw [projectAssertionsFromEntries?_skip
            (by intro f fr emb h; exact nomatch h)] at hpre
          rw [List.cons_append, projectAssertionsFromEntries?_skip
            (by intro f fr emb h; exact nomatch h)]
          exact ih hpre hpost
      | var v =>
          rw [projectAssertionsFromEntries?_skip
            (by intro f fr emb h; exact nomatch h)] at hpre
          rw [List.cons_append, projectAssertionsFromEntries?_skip
            (by intro f fr emb h; exact nomatch h)]
          exact ih hpre hpost
      | hyp ess f emb =>
          rw [projectAssertionsFromEntries?_skip
            (by intro f' fr' emb' h; exact nomatch h)] at hpre
          rw [List.cons_append, projectAssertionsFromEntries?_skip
            (by intro f' fr' emb' h; exact nomatch h)]
          exact ih hpre hpost

theorem projectAssertionsFromEntries?_split_inv {db : RuntimeDB} :
    ∀ {pre post : List (String × Metamath.Verify.Object)}
      {views : List AssertionView},
      projectAssertionsFromEntries? db (pre ++ post) = some views →
      ∃ vpre vpost,
        projectAssertionsFromEntries? db pre = some vpre ∧
          projectAssertionsFromEntries? db post = some vpost ∧
          views = vpre ++ vpost := by
  intro pre
  induction pre with
  | nil =>
      intro post views h
      rw [List.nil_append] at h
      exact ⟨[], views, rfl, h, rfl⟩
  | cons entry rest ih =>
      intro post views h
      obtain ⟨label, obj⟩ := entry
      cases obj with
      | assert f fr emb =>
          rw [List.cons_append] at h
          obtain ⟨view, vrest, hview, hvrest, rfl⟩ :=
            projectAssertionsFromEntries?_cons_assert_inv h
          obtain ⟨vpre, vpost, h1, h2, rfl⟩ := ih hvrest
          exact ⟨view :: vpre, vpost,
            projectAssertionsFromEntries?_cons_assert hview h1, h2,
            rfl⟩
      | const c =>
          rw [List.cons_append, projectAssertionsFromEntries?_skip
            (by intro f fr emb h; exact nomatch h)] at h
          obtain ⟨vpre, vpost, h1, h2, rfl⟩ := ih h
          exact ⟨vpre, vpost, by
            rw [projectAssertionsFromEntries?_skip
              (by intro f fr emb h; exact nomatch h)]
            exact h1, h2, rfl⟩
      | var v =>
          rw [List.cons_append, projectAssertionsFromEntries?_skip
            (by intro f fr emb h; exact nomatch h)] at h
          obtain ⟨vpre, vpost, h1, h2, rfl⟩ := ih h
          exact ⟨vpre, vpost, by
            rw [projectAssertionsFromEntries?_skip
              (by intro f fr emb h; exact nomatch h)]
            exact h1, h2, rfl⟩
      | hyp ess f emb =>
          rw [List.cons_append, projectAssertionsFromEntries?_skip
            (by intro f' fr' emb' h; exact nomatch h)] at h
          obtain ⟨vpre, vpost, h1, h2, rfl⟩ := ih h
          exact ⟨vpre, vpost, by
            rw [projectAssertionsFromEntries?_skip
              (by intro f' fr' emb' h; exact nomatch h)]
            exact h1, h2, rfl⟩

theorem projectAssertionsFromEntries?_resolves {db : RuntimeDB} :
    ∀ {entries : List (String × Metamath.Verify.Object)}
      {views : List AssertionView},
      projectAssertionsFromEntries? db entries = some views →
      ∀ e ∈ entries, ∀ (f : Metamath.Verify.Formula)
        (fr : RuntimeFrame) (emb : String), e.2 = .assert f fr emb →
        ∀ lbl ∈ fr.hyps.toList, db.find? lbl ≠ none := by
  intro entries
  induction entries with
  | nil =>
      intro views _ e he
      exact absurd he List.not_mem_nil
  | cons entry rest ih =>
      intro views h e he f fr emb hshape
      obtain ⟨label, obj⟩ := entry
      rcases List.mem_cons.mp he with rfl | htail
      · cases hshape
        obtain ⟨view, vrest, hview, -, -⟩ :=
          projectAssertionsFromEntries?_cons_assert_inv h
        exact projectAssertion?_resolves hview
      · cases obj with
        | assert f' fr' emb' =>
            obtain ⟨view, vrest, -, hvrest, -⟩ :=
              projectAssertionsFromEntries?_cons_assert_inv h
            exact ih hvrest e htail f fr emb hshape
        | const c =>
            rw [projectAssertionsFromEntries?_skip
              (by intro f' fr' emb' hcontra; exact nomatch hcontra)]
              at h
            exact ih h e htail f fr emb hshape
        | var v =>
            rw [projectAssertionsFromEntries?_skip
              (by intro f' fr' emb' hcontra; exact nomatch hcontra)]
              at h
            exact ih h e htail f fr emb hshape
        | hyp ess f' emb' =>
            rw [projectAssertionsFromEntries?_skip
              (by intro f'' fr'' emb'' hcontra; exact nomatch hcontra)]
              at h
            exact ih h e htail f fr emb hshape

/-! ## Label-sorted assertion algebra (the `≤` sort) -/

open Mettapedia.Languages.Metamath.SourceInferenceProjection in
theorem sortSourceAssertions_eq_of_perm
    {l₁ l₂ : List SourceAssertion} (hperm : l₁.Perm l₂)
    (hnodup : l₁.Pairwise (fun a b => a.label ≠ b.label)) :
    sortSourceAssertions l₁ = sortSourceAssertions l₂ := by
  have htrans : ∀ (a b c : SourceAssertion),
      (decide (a.label ≤ b.label)) → (decide (b.label ≤ c.label)) →
        (decide (a.label ≤ c.label) : Bool) := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    exact le_trans hab hbc
  have htotal : ∀ (a b : SourceAssertion),
      (decide (a.label ≤ b.label) ||
        decide (b.label ≤ a.label) : Bool) := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total a.label b.label
  have hs₁ := List.pairwise_mergeSort htrans htotal l₁
  have hs₂ := List.pairwise_mergeSort htrans htotal l₂
  have hp₁ := List.mergeSort_perm l₁
    (fun a b => a.label ≤ b.label)
  have hp₂ := List.mergeSort_perm l₂
    (fun a b => a.label ≤ b.label)
  have hnodup₁ :
      (sortSourceAssertions l₁).Pairwise
        (fun a b => a.label ≠ b.label) :=
    (hp₁.pairwise_iff (fun h heq => h heq.symm)).mpr hnodup
  have hnodup₂ :
      (sortSourceAssertions l₂).Pairwise
        (fun a b => a.label ≠ b.label) :=
    (hp₂.pairwise_iff (fun h heq => h heq.symm)).mpr
      ((hperm.pairwise_iff (fun h heq => h heq.symm)).mp hnodup)
  have hlt₁ : (sortSourceAssertions l₁).Pairwise
      (fun a b => a.label < b.label) := by
    have := hs₁.and hnodup₁
    exact this.imp (fun ⟨hle, hne⟩ =>
      lt_of_le_of_ne (by simpa using hle) hne)
  have hlt₂ : (sortSourceAssertions l₂).Pairwise
      (fun a b => a.label < b.label) := by
    have := hs₂.and hnodup₂
    exact this.imp (fun ⟨hle, hne⟩ =>
      lt_of_le_of_ne (by simpa using hle) hne)
  have hperm' :
      (sortSourceAssertions l₁).Perm (sortSourceAssertions l₂) :=
    (hp₁.trans hperm).trans hp₂.symm
  exact eq_of_perm_of_pairwise_lt
    (fun a b hab hba => absurd (lt_trans hab hba) (lt_irrefl _))
    hperm' hlt₁ hlt₂

open Mettapedia.Languages.Metamath.SourceInferenceProjection in
/-- Appending a fresh-labeled assertion splits the label-sorted list at
its ordered position. -/
theorem sortSourceAssertions_append_fresh
    {assertions : List SourceAssertion} {a : SourceAssertion}
    (hnodup : assertions.Pairwise (fun x y => x.label ≠ y.label))
    (hfresh : ∀ x ∈ assertions, a.label ≠ x.label) :
    ∃ pre post,
      sortSourceAssertions assertions = pre ++ post ∧
        sortSourceAssertions (assertions ++ [a]) =
          pre ++ a :: post ∧
        ∀ x ∈ pre, ¬(a.label ≤ x.label) := by
  have htrans : ∀ (x y z : SourceAssertion),
      (decide (x.label ≤ y.label)) → (decide (y.label ≤ z.label)) →
        (decide (x.label ≤ z.label) : Bool) := by
    intro x y z hxy hyz
    simp only [decide_eq_true_eq] at *
    exact le_trans hxy hyz
  have htotal : ∀ (x y : SourceAssertion),
      (decide (x.label ≤ y.label) ||
        decide (y.label ≤ x.label) : Bool) := by
    intro x y
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total x.label y.label
  obtain ⟨pre, post, hsplit₁, hsplit₂, hpre⟩ :=
    List.mergeSort_cons htrans htotal a assertions
  have hperm : (assertions ++ [a]).Perm (a :: assertions) := by
    simp
  have hnodup' : (assertions ++ [a]).Pairwise
      (fun x y => x.label ≠ y.label) := by
    rw [List.pairwise_append]
    refine ⟨hnodup, by simp, ?_⟩
    intro x hx y hy
    rcases List.mem_singleton.mp hy with rfl
    exact fun heq => hfresh x hx heq.symm
  refine ⟨pre, post, ?_, ?_, ?_⟩
  · exact hsplit₂ ▸ rfl
  · have heq : sortSourceAssertions (assertions ++ [a]) =
        sortSourceAssertions (a :: assertions) :=
      sortSourceAssertions_eq_of_perm hperm hnodup'
    rw [heq]
    exact hsplit₁
  · intro x hx
    have := hpre x hx
    simpa using this

/-! ## Source validity survives canonicalization (Ingredient B) -/

section ValidityTransport

open Mettapedia.Languages.Metamath.SourceInferenceProjection

private theorem contains_sortStrings (l : List String) (x : String) :
    (sortStrings l).contains x = l.contains x := by
  by_cases h : x ∈ l
  · simp [h, (mem_sortStrings_iff x l).mpr h]
  · have h' : x ∉ sortStrings l := fun hc =>
      h ((mem_sortStrings_iff x l).mp hc)
    simp [h, h']

private theorem all_congr_fun {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.all p = l.all q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro h
      simp only [List.all_cons, h a (by simp),
        ih (fun x hx => h x (by simp [hx]))]

private theorem all_perm {α : Type _} {l₁ l₂ : List α}
    (hperm : l₁.Perm l₂) (p : α → Bool) : l₁.all p = l₂.all p := by
  by_cases h : ∀ x ∈ l₁, p x = true
  · rw [List.all_eq_true.mpr h, List.all_eq_true.mpr
      (fun x hx => h x (hperm.mem_iff.mpr hx))]
  · have h₂ : ¬∀ x ∈ l₂, p x = true := fun hall =>
      h (fun x hx => hall x (hperm.mem_iff.mp hx))
    cases hb₁ : l₁.all p
    · cases hb₂ : l₂.all p
      · rfl
      · exact absurd (List.all_eq_true.mp hb₂) h₂
    · exact absurd (List.all_eq_true.mp hb₁) h

private theorem nodupBool_perm {l₁ l₂ : List String}
    (hperm : l₁.Perm l₂) :
    (l₁.eraseDups.length == l₁.length) =
      (l₂.eraseDups.length == l₂.length) := by
  by_cases h : l₁.Nodup
  · rw [beq_iff_eq.mpr (eraseDups_length_eq_of_nodup _ h),
      beq_iff_eq.mpr
        (eraseDups_length_eq_of_nodup _ (hperm.nodup_iff.mp h))]
  · have h₂ : ¬l₂.Nodup := fun hn => h (hperm.nodup_iff.mpr hn)
    cases hb₁ : (l₁.eraseDups.length == l₁.length)
    · cases hb₂ : (l₂.eraseDups.length == l₂.length)
      · rfl
      · exact absurd
          (nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp hb₂)) h₂
    · exact absurd
        (nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp hb₁)) h

private theorem respectDecls_sortStrings
    (c v : List String) (f : ConstantHeadedFormula) :
    formulaSymbolsRespectDeclarations (sortStrings c) (sortStrings v)
      f = formulaSymbolsRespectDeclarations c v f := by
  unfold formulaSymbolsRespectDeclarations
  rw [contains_sortStrings]
  congr 1
  apply all_congr_fun
  intro sym _
  cases sym with
  | const name => exact contains_sortStrings c name
  | var name => exact contains_sortStrings v name

private theorem assertionValid_sortStrings (c v : List String)
    (a : SourceAssertion) :
    sourceAssertionValid (sortStrings c) (sortStrings v) a =
      sourceAssertionValid c v a := by
  unfold sourceAssertionValid
  rw [respectDecls_sortStrings]
  have hhyps : a.hypotheses.all
      (formulaSymbolsRespectDeclarations (sortStrings c)
        (sortStrings v) ∘ HypothesisView.formula) =
      a.hypotheses.all
        (formulaSymbolsRespectDeclarations c v ∘
          HypothesisView.formula) := by
    apply all_congr_fun
    intro hyp _
    simp only [Function.comp_apply]
    exact respectDecls_sortStrings c v hyp.formula
  rw [hhyps]

/-- Canonicalizing the checker view preserves source-prefix validity. -/
theorem sourcePrefixValid_runtimePrefix (state : SourceState) :
    sourcePrefixValid (runtimePrefix state) =
      sourcePrefixValid state.toSourcePrefix := by
  have hpermC : (sortStrings state.declaredConstants).Perm
      state.declaredConstants :=
    List.mergeSort_perm state.declaredConstants _
  have hpermV : (sortStrings state.declaredVariables).Perm
      state.declaredVariables :=
    List.mergeSort_perm state.declaredVariables _
  have hpermA : (sortSourceAssertions state.assertions).Perm
      state.assertions :=
    List.mergeSort_perm state.assertions _
  have e₁ := nodupBool_perm hpermC
  have e₂ := nodupBool_perm hpermV
  have e₃ : (sortStrings state.declaredConstants).all
      (fun c => !(sortStrings state.declaredVariables).contains c) =
      state.declaredConstants.all
        (fun c => !state.declaredVariables.contains c) := by
    rw [all_perm hpermC]
    apply all_congr_fun
    intro c _
    rw [contains_sortStrings]
  have e₄ : state.activeHypotheses.all
      (formulaSymbolsRespectDeclarations
        (sortStrings state.declaredConstants)
        (sortStrings state.declaredVariables) ∘
          HypothesisView.formula) =
      state.activeHypotheses.all
        (formulaSymbolsRespectDeclarations state.declaredConstants
          state.declaredVariables ∘ HypothesisView.formula) := by
    apply all_congr_fun
    intro hyp _
    simp only [Function.comp_apply]
    exact respectDecls_sortStrings _ _ hyp.formula
  have e₅ : (sortSourceAssertions state.assertions).all
      (sourceAssertionValid (sortStrings state.declaredConstants)
        (sortStrings state.declaredVariables)) =
      state.assertions.all
        (sourceAssertionValid state.declaredConstants
          state.declaredVariables) := by
    rw [all_perm hpermA]
    apply all_congr_fun
    intro a _
    exact assertionValid_sortStrings _ _ a
  have hpermL : ((state.activeHypotheses.map HypothesisView.label) ++
      (sortSourceAssertions state.assertions).map
        SourceAssertion.label).Perm
      ((state.activeHypotheses.map HypothesisView.label) ++
        state.assertions.map SourceAssertion.label) :=
    List.Perm.append_left _ (hpermA.map SourceAssertion.label)
  have e₆ : sourceRuleLabelsValid
      (sourcePrefixRuleLabels (runtimePrefix state)) =
      sourceRuleLabelsValid
        (sourcePrefixRuleLabels state.toSourcePrefix) := by
    unfold sourceRuleLabelsValid sourcePrefixRuleLabels
    simp only [runtimePrefix, SourceState.toSourcePrefix]
    rw [all_perm hpermL, nodupBool_perm hpermL]
  unfold sourcePrefixValid
  simp only [runtimePrefix, SourceState.toSourcePrefix] at e₆ ⊢
  rw [e₁, e₂, e₃, e₄, e₅, e₆]

/-- Ingredient B: a valid source state's canonical checker view passes
the projection recheck. -/
theorem prefixProjectionValid_runtimePrefix {state : SourceState}
    (hvalid : sourceStateValid state = true) :
    prefixProjectionValid (runtimePrefix state).toProjection = true := by
  rw [← sourcePrefixValid_eq_runtime, sourcePrefixValid_runtimePrefix]
  exact sourcePrefixValid_of_sourceStateValid state hvalid

end ValidityTransport
/-! ## Active hypotheses project to themselves (Ingredient A) -/

section ActiveProjection

open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity

private theorem forall₂_map_self
    {R : String → HypothesisView → Prop} :
    ∀ {hyps : List HypothesisView},
      List.Forall₂ R (hyps.map HypothesisView.label) hyps →
      ∀ hyp ∈ hyps, R hyp.label hyp := by
  intro hyps
  induction hyps with
  | nil =>
      intro _ hyp hh
      exact absurd hh List.not_mem_nil
  | cons a rest ih =>
      intro h hyp hh
      rw [List.map_cons] at h
      cases h with
      | cons hR htail =>
          rcases List.mem_cons.mp hh with rfl | hmem
          · exact hR
          · exact ih htail hyp hmem

/-- Under agreement, every active hypothesis projects to itself in
the scope-erased database. -/
theorem activeHyp_project_self_pdb {db : RuntimeDB}
    {state : SourceState} (agreement : RuntimeDBAgrees db state) :
    ∀ hyp ∈ state.activeHypotheses,
      projectHypothesis? (projectionDB db) hyp.label = some hyp := by
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj
  obtain ⟨-, -, -, -, -, -, hyps, hhyps, -, asserts, -, -, hrec⟩ :=
    projectPrefix?_ok_inv hproj
  have hact : hyps = state.activeHypotheses := by
    have := congrArg PrefixProjection.activeHypotheses hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  subst hact
  have hlabels : (projectionDB db).frame.hyps.toList =
      state.activeHypotheses.map HypothesisView.label :=
    agreement.rawFrame.2
  rw [hlabels] at hhyps
  exact forall₂_map_self
    (projectHypotheses?_forall₂ (projectionDB db) _ _ hhyps)

/-- Under agreement, every active hypothesis projects to itself. -/
theorem activeHyp_project_self {db : RuntimeDB} {state : SourceState}
    (agreement : RuntimeDBAgrees db state) :
    ∀ hyp ∈ state.activeHypotheses,
      projectHypothesis? db hyp.label = some hyp := by
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj
  obtain ⟨-, -, -, -, -, -, hyps, hhyps, -, asserts, -, -, hrec⟩ :=
    projectPrefix?_ok_inv hproj
  have hact : hyps = state.activeHypotheses := by
    have := congrArg PrefixProjection.activeHypotheses hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  subst hact
  have hlabels : (projectionDB db).frame.hyps.toList =
      state.activeHypotheses.map HypothesisView.label :=
    agreement.rawFrame.2
  rw [hlabels] at hhyps
  have hforall := projectHypotheses?_forall₂ (projectionDB db) _ _ hhyps
  have hpoint := forall₂_map_self hforall
  intro hyp hh
  have := hpoint hyp hh
  rwa [projectHypothesis?_congr
    (db := db) (db' := projectionDB db) rfl] at this

/-- The freshly inserted assertion projects to its source view. -/
theorem projectAssertion?_new {db : RuntimeDB} {state : SourceState}
    {label : String} {formula : ConstantHeadedFormula}
    (hpoint : ∀ hyp ∈ mandatoryHypotheses state formula,
      projectHypothesis? db hyp.label = some hyp)
    (hvalid : sourceAssertionValid state.declaredConstants
      state.declaredVariables (sourceAssertion state label formula) =
        true) :
    projectAssertion? db label formula.toRuntime
      (mandatoryFrame state formula).toRuntime label =
      some (sourceAssertion state label formula).toProjectionView := by
  have hmapM : projectHypotheses? db
      ((mandatoryFrame state formula).toRuntime).hyps.toList =
      some (mandatoryHypotheses state formula) := by
    have hlist : ((mandatoryFrame state formula).toRuntime).hyps.toList
        = (mandatoryHypotheses state formula).map
            HypothesisView.label := by
      simp [SourceFrame.toRuntime, mandatoryFrame]
    rw [hlist]
    have hp := hpoint
    clear hlist hvalid hpoint
    revert hp
    generalize mandatoryHypotheses state formula = mhyps
    induction mhyps with
    | nil => intro _; rfl
    | cons a rest ih =>
        intro hp
        unfold projectHypotheses? at ih ⊢
        rw [List.map_cons, List.mapM_cons, hp a (by simp),
          ih (fun x hx => hp x (by simp [hx]))]
        rfl
  have hform : ConstantHeadedFormula.ofRuntime? formula.toRuntime =
      some formula :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mpr rfl
  simp only [sourceAssertionValid, Bool.and_eq_true] at hvalid
  obtain ⟨⟨⟨hfv, hrf⟩, -⟩, -⟩ := hvalid
  have hframe : frameProjectionValid
      (mandatoryFrame state formula).toRuntime
      (mandatoryHypotheses state formula) = true := by
    rw [← sourceFrameValid_eq_runtime]
    exact hfv
  have hrespect : formulaSymbolsRespectFrame
      (floatingVariableNames (mandatoryHypotheses state formula))
      formula = true := hrf
  simp [projectAssertion?, guard, hform, hmapM, hframe, hrespect,
    sourceAssertion, SourceAssertion.toProjectionView]

end ActiveProjection

/-! ## Assembly glue -/

section AssemblyGlue

open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- Two boundary splits of one list coincide. -/
theorem split_unique {α : Type _} {P : α → Prop}
    [DecidablePred P] :
    ∀ {p₁ q₁ p₂ q₂ : List α}, p₁ ++ q₁ = p₂ ++ q₂ →
      (∀ x ∈ p₁, P x) → (∀ x ∈ q₁, ¬P x) →
      (∀ x ∈ p₂, P x) → (∀ x ∈ q₂, ¬P x) →
      p₁ = p₂ ∧ q₁ = q₂ := by
  intro p₁
  induction p₁ with
  | nil =>
      intro q₁ p₂ q₂ heq _ hq₁ hp₂ _
      cases p₂ with
      | nil => exact ⟨rfl, by simpa using heq⟩
      | cons b t =>
          rw [List.nil_append] at heq
          subst heq
          exact absurd (hp₂ b (by simp)) (hq₁ b (by simp))
  | cons a t ih =>
      intro q₁ p₂ q₂ heq hp₁ hq₁ hp₂ hq₂
      cases p₂ with
      | nil =>
          rw [List.nil_append] at heq
          subst heq
          exact absurd (hp₁ a (by simp)) (hq₂ a (by simp))
      | cons b t₂ =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, heq⟩ := heq
          obtain ⟨h1, h2⟩ := ih heq
            (fun x hx => hp₁ x (by simp [hx])) hq₁
            (fun x hx => hp₂ x (by simp [hx])) hq₂
          exact ⟨by rw [h1], h2⟩

/-- Constants pass through an assert entry untouched. -/
theorem declaredConstantNames_append
    (l₁ l₂ : List (String × Metamath.Verify.Object)) :
    declaredConstantNames (l₁ ++ l₂) =
      declaredConstantNames l₁ ++ declaredConstantNames l₂ := by
  unfold declaredConstantNames
  exact List.filterMap_append

theorem declaredVariableNames_append
    (l₁ l₂ : List (String × Metamath.Verify.Object)) :
    declaredVariableNames (l₁ ++ l₂) =
      declaredVariableNames l₁ ++ declaredVariableNames l₂ := by
  unfold declaredVariableNames
  exact List.filterMap_append

@[simp] theorem declaredConstantNames_cons_assert
    (l : String) (f : Metamath.Verify.Formula) (fr : RuntimeFrame)
    (e : String) (rest : List (String × Metamath.Verify.Object)) :
    declaredConstantNames ((l, .assert f fr e) :: rest) =
      declaredConstantNames rest := rfl

@[simp] theorem declaredVariableNames_cons_assert
    (l : String) (f : Metamath.Verify.Formula) (fr : RuntimeFrame)
    (e : String) (rest : List (String × Metamath.Verify.Object)) :
    declaredVariableNames ((l, .assert f fr e) :: rest) =
      declaredVariableNames rest := rfl

/-- The proof-facing caller frame is stable under fresh insertion when
the frame's hypothesis labels resolve. -/
theorem proofFacingCallerFrame_insertObj {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none)
    (hres : ∀ lbl ∈ db.frame.hyps.toList, db.find? lbl ≠ none) :
    proofFacingCallerFrame (insertObj db l obj) =
      proofFacingCallerFrame db := by
  unfold proofFacingCallerFrame
  rw [show (insertObj db l obj).frame = db.frame from rfl]
  rw [show (insertObj db l obj).frameFloatVars db.frame =
      db.frameFloatVars db.frame from
    frameFloatVars_insertObj hfresh hres]

/-- Mandatory hypotheses are active hypotheses. -/
theorem mandatoryHypotheses_subset {state : SourceState}
    {formula : ConstantHeadedFormula} :
    ∀ hyp ∈ mandatoryHypotheses state formula,
      hyp ∈ state.activeHypotheses := by
  intro hyp hh
  unfold mandatoryHypotheses at hh
  exact List.mem_of_mem_filter hh

/-- The embedded-name guard survives the split insertion. -/
theorem embeddedNames_split {pre post :
    List (String × Metamath.Verify.Object)} {l : String}
    {obj : Metamath.Verify.Object}
    (hall : ((pre ++ post).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true)
    (hnew : objectEmbeddedNameMatches l obj = true) :
    ((pre ++ (l, obj) :: post).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true := by
  rw [List.all_eq_true] at hall ⊢
  intro e he
  rcases List.mem_append.mp he with hpre | hrest
  · exact hall e (List.mem_append_left _ hpre)
  · rcases List.mem_cons.mp hrest with rfl | hpost
    · exact hnew
    · exact hall e (List.mem_append_right _ hpost)

end AssemblyGlue

/-! ## Runtime float variables of a pointwise-projected frame -/

section FloatVars

open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity

theorem frameFloatVars_of_pointwise {db : RuntimeDB}
    {hyps : List HypothesisView} {dj : Array (String × String)}
    (hpoint : ∀ hyp ∈ hyps,
      projectHypothesis? db hyp.label = some hyp) :
    db.frameFloatVars
      { dj := dj, hyps := (hyps.map HypothesisView.label).toArray } =
      floatingVariableNames hyps := by
  unfold DB.frameFloatVars floatingVariableNames
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro hyp hh
  obtain ⟨rf, hfind, hform, -⟩ :=
    projectHypothesis?_eq_some_fidelity db hyp.label hyp
      (hpoint hyp hh)
  simp only [Function.comp_apply]
  rw [hfind]
  cases hyp with
  | essential lbl f =>
      simp [hypothesisEssentialBit, HypothesisView.floatingVariable?]
  | floating lbl typecode variableName =>
      simp only [hypothesisEssentialBit]
      have hrf : rf = (⟨typecode, [.var variableName]⟩ :
          ConstantHeadedFormula).toRuntime :=
        (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
          simpa [HypothesisView.formula] using hform)
      subst hrf
      simp [ConstantHeadedFormula.toRuntime, Formula.isFloatShape,
        HypothesisView.floatingVariable?]

end FloatVars

/-! ## New-frame guard bridges -/

section NewFrameGuards

open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity

theorem toRuntime_hasConstHead (f : ConstantHeadedFormula) :
    f.toRuntime.hasConstHead = true := by
  simp [ConstantHeadedFormula.toRuntime, Formula.hasConstHead]

theorem hypOK?_of_pointwise {db : RuntimeDB} {hyp : HypothesisView}
    (hpoint : projectHypothesis? db hyp.label = some hyp) :
    db.hypOK? hyp.label = true := by
  obtain ⟨rf, hfind, hform, -⟩ :=
    projectHypothesis?_eq_some_fidelity db hyp.label hyp hpoint
  rw [DB.hypOK?, hfind]
  cases hyp with
  | essential lbl f =>
      have hrf : rf = f.toRuntime :=
        (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
          simpa [HypothesisView.formula] using hform)
      subst hrf
      simp only [hypothesisEssentialBit, if_true]
      exact toRuntime_hasConstHead f
  | floating lbl typecode variableName =>
      have hrf : rf = (⟨typecode, [.var variableName]⟩ :
          ConstantHeadedFormula).toRuntime :=
        (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
          simpa [HypothesisView.formula] using hform)
      subst hrf
      simp [hypothesisEssentialBit, ConstantHeadedFormula.toRuntime,
        Formula.isFloatShape]

theorem frameHypsOk?_of_pointwise {db : RuntimeDB}
    {hyps : List HypothesisView} {dj : Array (String × String)}
    (hpoint : ∀ hyp ∈ hyps,
      projectHypothesis? db hyp.label = some hyp) :
    db.frameHypsOk?
      { dj := dj, hyps := (hyps.map HypothesisView.label).toArray } =
      true := by
  rw [DB.frameHypsOk?, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  simp only [List.size_toArray, List.length_map] at hi
  have hbang : ((hyps.map HypothesisView.label).toArray)[i]! =
      hyps[i].label := by
    rw [getElem!_pos _ i (by simpa using hi)]
    simp
  show db.hypOK? ((hyps.map HypothesisView.label).toArray)[i]! = true
  rw [hbang]
  exact hypOK?_of_pointwise (hpoint hyps[i] (List.getElem_mem hi))

private theorem pairwise_of_nodup_filterMap {α β : Type _}
    {f : α → Option β} :
    ∀ {l : List α}, (l.filterMap f).Nodup →
      l.Pairwise (fun a b => ∀ x y,
        f a = some x → f b = some y → x ≠ y) := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a rest ih =>
      intro h
      cases hfa : f a with
      | none =>
          rw [List.filterMap_cons, hfa] at h
          refine List.Pairwise.cons ?_ (ih h)
          intro b _ x y hx _ _
          rw [hfa] at hx
          exact nomatch hx
      | some va =>
          rw [List.filterMap_cons, hfa] at h
          obtain ⟨hnot, htail⟩ := List.nodup_cons.mp h
          refine List.Pairwise.cons ?_ (ih htail)
          intro b hb x y hx hy heq
          rw [hfa] at hx
          cases Option.some.inj hx
          subst heq
          exact hnot (List.mem_filterMap.mpr ⟨b, hb, hy⟩)

theorem frameFloatVarsUnique?_of_pointwise {db : RuntimeDB}
    {hyps : List HypothesisView} {dj : Array (String × String)}
    (hpoint : ∀ hyp ∈ hyps,
      projectHypothesis? db hyp.label = some hyp)
    (huniq : hasUniqueFloatingVariables hyps = true) :
    db.frameFloatVarsUnique?
      { dj := dj, hyps := (hyps.map HypothesisView.label).toArray } =
      true := by
  have hnodup :
      (hyps.filterMap HypothesisView.floatingVariable?).Nodup := by
    apply nodup_of_eraseDups_length_eq
    have := huniq
    simp only [hasUniqueFloatingVariables, floatingVariableNames,
      beq_iff_eq] at this
    exact this
  have hpair := pairwise_of_nodup_filterMap hnodup
  have hpairGet := List.pairwise_iff_getElem.mp hpair
  rw [DB.frameFloatVarsUnique?]
  simp only [List.size_toArray, List.length_map]
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hi hj
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, dite_false]
    have hbi : ((hyps.map HypothesisView.label).toArray)[i]! =
        hyps[i].label := by
      rw [getElem!_pos _ i (by simpa using hi)]
      simp
    have hbj : ((hyps.map HypothesisView.label).toArray)[j]! =
        hyps[j].label := by
      rw [getElem!_pos _ j (by simpa using hj)]
      simp
    rw [hbi, hbj]
    have hne : ∀ x y,
        HypothesisView.floatingVariable? hyps[i] = some x →
        HypothesisView.floatingVariable? hyps[j] = some y →
        x ≠ y := by
      rcases Nat.lt_trichotomy i j with hlt | heq | hgt
      · exact hpairGet i j hi hj hlt
      · exact absurd heq hij
      · exact fun x y hx hy heq =>
          hpairGet j i hj hi hgt y x hy hx heq.symm
    obtain ⟨rfi, hfindi, hformi, -⟩ :=
      projectHypothesis?_eq_some_fidelity db hyps[i].label hyps[i]
        (hpoint hyps[i] (List.getElem_mem hi))
    obtain ⟨rfj, hfindj, hformj, -⟩ :=
      projectHypothesis?_eq_some_fidelity db hyps[j].label hyps[j]
        (hpoint hyps[j] (List.getElem_mem hj))
    rw [hfindi, hfindj]
    cases hci : hyps[i] with
    | essential lbl_i f_i =>
        simp [hypothesisEssentialBit]
    | floating lbl_i tc_i v_i =>
        cases hcj : hyps[j] with
        | essential lbl_j f_j =>
            simp [hypothesisEssentialBit]
        | floating lbl_j tc_j v_j =>
            have hrfi : rfi = (⟨tc_i, [.var v_i]⟩ :
                ConstantHeadedFormula).toRuntime := by
              rw [hci] at hformi
              exact (ConstantHeadedFormula.ofRuntime?_eq_some_iff
                _ _).mp (by
                  simpa [HypothesisView.formula] using hformi)
            have hrfj : rfj = (⟨tc_j, [.var v_j]⟩ :
                ConstantHeadedFormula).toRuntime := by
              rw [hcj] at hformj
              exact (ConstantHeadedFormula.ofRuntime?_eq_some_iff
                _ _).mp (by
                  simpa [HypothesisView.formula] using hformj)
            have hvne : v_i ≠ v_j := by
              refine hne v_i v_j ?_ ?_
              · rw [hci]; rfl
              · rw [hcj]; rfl
            subst hrfi hrfj
            simp [hypothesisEssentialBit,
              Formula.floatVarsDistinct?, Formula.floatVarName,
              ConstantHeadedFormula.toRuntime, hvne]

open Mettapedia.Languages.Metamath.SourceGSLTState in
theorem frameDvVars_of_pointwise {db : RuntimeDB}
    {state : SourceState} {formula : ConstantHeadedFormula}
    (hpoint : ∀ hyp ∈ mandatoryHypotheses state formula,
      projectHypothesis? db hyp.label = some hyp)
    (hdv : sourceFrameDVValid (mandatoryFrame state formula)
      (floatingVariableNames (mandatoryHypotheses state formula)) =
        true) :
    db.frameDvVarsInFrame? (mandatoryFrame state formula).toRuntime =
      true := by
  have hfloats : db.frameFloatVars
      (mandatoryFrame state formula).toRuntime =
      floatingVariableNames (mandatoryHypotheses state formula) := by
    have := frameFloatVars_of_pointwise
      (dj :=
        (mandatoryFrame state formula).distinctVariables.toArray)
      hpoint
    simpa [SourceFrame.toRuntime, mandatoryFrame] using this
  rw [DB.frameDvVarsInFrame?, hfloats]
  have hdj : ((mandatoryFrame state formula).toRuntime).dj.toList =
      (mandatoryFrame state formula).distinctVariables := by
    simp [SourceFrame.toRuntime]
  rw [hdj, List.all_eq_true]
  rw [sourceFrameDVValid, List.all_eq_true] at hdv
  intro p hp
  have hpair := hdv p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpair ⊢
  exact ⟨List.mem_of_elem_eq_true hpair.1.2,
    List.mem_of_elem_eq_true hpair.2⟩

end NewFrameGuards

/-! ## The assert-lane discharge -/

section AssertLane

open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- The inserted database, in `insertObj` form. -/
theorem insert_assert_eq_insertObj {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (inserted : insertAssertion? before label formula = some after)
    (pos : Pos) :
    db.insert pos label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime) =
      insertObj db label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label) := by
  exact runtimeInsert_eq_of_sourceInsert agreement inserted pos

/-- Freshness of the source label in the runtime map. -/
theorem fresh_of_sourceInsert {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (inserted : insertAssertion? before label formula = some after) :
    db.find? label = none :=
  runtimeLabelFresh_of_sourceInsert agreement inserted

/-- Pointwise projection of mandatory hypotheses, in the inserted
database. -/
theorem mandatory_pointwise_inserted {db : RuntimeDB}
    {before : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {obj : Metamath.Verify.Object}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? label = none) :
    ∀ hyp ∈ mandatoryHypotheses before formula,
      projectHypothesis? (insertObj db label obj) hyp.label =
        some hyp := by
  intro hyp hh
  have hself := activeHyp_project_self agreement hyp
    (mandatoryHypotheses_subset hyp hh)
  rw [projectHypothesis?_congr (db := db)
    (db' := insertObj db label obj)
    (find?_insertObj_occupied hfresh
      (projectHypothesis?_resolves hself))]
  exact hself

/-- The freshly inserted assertion is valid in the after-state. -/
theorem newAssert_valid {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (inserted : insertAssertion? before label formula = some after) :
    sourceAssertionValid before.declaredConstants
      before.declaredVariables
      (sourceAssertion before label formula) = true := by
  have hvalid := insertAssertion?_valid inserted
  have hshape := insertAssertion?_eq_some_state inserted
  have hprefix := sourcePrefixValid_of_sourceStateValid after hvalid
  rw [sourcePrefixValid] at hprefix
  have hall : after.toSourcePrefix.assertions.all
      (sourceAssertionValid after.toSourcePrefix.declaredConstants
        after.toSourcePrefix.declaredVariables) = true := by
    simp only [Bool.and_eq_true] at hprefix
    exact hprefix.1.2
  rw [List.all_eq_true] at hall
  have hmem : sourceAssertion before label formula ∈
      after.toSourcePrefix.assertions := by
    rw [hshape]
    simp [SourceState.toSourcePrefix]
  have := hall _ hmem
  rw [hshape] at this
  simpa [SourceState.toSourcePrefix] using this

/-- The new assert object passes its own well-formedness check in the
inserted database. -/
theorem newAssert_wellFormedObj {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (inserted : insertAssertion? before label formula = some after) :
    (insertObj db label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime
          label)).wellFormedObj? label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label) = true := by
  have hfresh := fresh_of_sourceInsert agreement inserted
  have hpoint := mandatory_pointwise_inserted
    (obj := .assert formula.toRuntime
      (mandatoryFrame before formula).toRuntime label)
    (formula := formula) agreement hfresh
  have hvalid := newAssert_valid inserted
  simp only [sourceAssertionValid, Bool.and_eq_true] at hvalid
  obtain ⟨⟨⟨hfv, -⟩, -⟩, -⟩ := hvalid
  have huniq : hasUniqueFloatingVariables
      (mandatoryHypotheses before formula) = true := by
    have hsfv : sourceFrameValid (mandatoryFrame before formula)
        (mandatoryHypotheses before formula) = true := hfv
    simp only [sourceFrameValid, Bool.and_eq_true] at hsfv
    exact hsfv.1.1.1.1.2
  rw [DB.wellFormedObj?, Bool.and_eq_true]
  refine ⟨toRuntime_hasConstHead formula, ?_⟩
  rw [DB.wellFormedFrame?, Bool.and_eq_true]
  constructor
  · have := frameHypsOk?_of_pointwise
      (db := insertObj db label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))
      (dj := (mandatoryFrame before formula).distinctVariables.toArray)
      hpoint
    simpa [SourceFrame.toRuntime, mandatoryFrame] using this
  · have := frameFloatVarsUnique?_of_pointwise
      (db := insertObj db label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))
      (dj := (mandatoryFrame before formula).distinctVariables.toArray)
      hpoint huniq
    simpa [SourceFrame.toRuntime, mandatoryFrame] using this

/-- Collector views carry their entry keys as labels. -/
theorem projectAssertionsFromEntries?_labels {db : RuntimeDB} :
    ∀ {entries : List (String × Metamath.Verify.Object)}
      {views : List AssertionView},
      projectAssertionsFromEntries? db entries = some views →
      views.map AssertionView.label =
        (entries.filterMap fun e =>
          match e.2 with
          | .assert _ _ _ => some e.1
          | _ => none) := by
  intro entries
  induction entries with
  | nil =>
      intro views h
      cases Option.some.inj h
      rfl
  | cons entry rest ih =>
      intro views h
      obtain ⟨label, obj⟩ := entry
      cases obj with
      | assert f fr emb =>
          obtain ⟨view, vrest, hview, hvrest, rfl⟩ :=
            projectAssertionsFromEntries?_cons_assert_inv h
          have hlabel : view.label = label := by
            unfold projectAssertion? at hview
            obtain ⟨-, hview⟩ := guard_bind_some hview
            obtain ⟨fm, -, hview⟩ := bind_some_inv hview
            obtain ⟨hs, -, hview⟩ := bind_some_inv hview
            obtain ⟨-, hview⟩ := guard_bind_some hview
            obtain ⟨-, hview⟩ := guard_bind_some hview
            cases Option.some.inj hview
            rfl
          simp only [List.map_cons, List.filterMap_cons, hlabel,
            ih hvrest]
      | const c =>
          rw [projectAssertionsFromEntries?_skip
            (by intro f fr emb hc; exact nomatch hc)] at h
          simpa using ih h
      | var v =>
          rw [projectAssertionsFromEntries?_skip
            (by intro f fr emb hc; exact nomatch hc)] at h
          simpa using ih h
      | hyp ess f emb =>
          rw [projectAssertionsFromEntries?_skip
            (by intro f' fr' emb' hc; exact nomatch hc)] at h
          simpa using ih h

/-- Pointwise mandatory projection in the scope-erased inserted
database. -/
theorem mandatory_pointwise_inserted_pdb {db : RuntimeDB}
    {before : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {obj : Metamath.Verify.Object}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? label = none) :
    ∀ hyp ∈ mandatoryHypotheses before formula,
      projectHypothesis?
        (insertObj (projectionDB db) label obj) hyp.label =
        some hyp := by
  intro hyp hh
  have hself := activeHyp_project_self_pdb agreement hyp
    (mandatoryHypotheses_subset hyp hh)
  rw [projectHypothesis?_congr (db := projectionDB db)
    (db' := insertObj (projectionDB db) label obj)
    (find?_insertObj_occupied (db := projectionDB db) hfresh
      (projectHypothesis?_resolves hself))]
  exact hself

/-- The new assert object's own check, over any base carrying the
pointwise mandatory projections. -/
theorem newAssert_wellFormedObj_of_pointwise {db₀ : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (inserted : insertAssertion? before label formula = some after)
    (hpoint : ∀ hyp ∈ mandatoryHypotheses before formula,
      projectHypothesis?
        (insertObj db₀ label
          (.assert formula.toRuntime
            (mandatoryFrame before formula).toRuntime label))
        hyp.label = some hyp) :
    (insertObj db₀ label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime
          label)).wellFormedObj? label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label) = true := by
  have hvalid := newAssert_valid inserted
  simp only [sourceAssertionValid, Bool.and_eq_true] at hvalid
  obtain ⟨⟨⟨hfv, -⟩, -⟩, -⟩ := hvalid
  have huniq : hasUniqueFloatingVariables
      (mandatoryHypotheses before formula) = true := by
    have hsfv : sourceFrameValid (mandatoryFrame before formula)
        (mandatoryHypotheses before formula) = true := hfv
    simp only [sourceFrameValid, Bool.and_eq_true] at hsfv
    exact hsfv.1.1.1.1.2
  rw [DB.wellFormedObj?, Bool.and_eq_true]
  refine ⟨toRuntime_hasConstHead formula, ?_⟩
  rw [DB.wellFormedFrame?, Bool.and_eq_true]
  constructor
  · have := frameHypsOk?_of_pointwise
      (db := insertObj db₀ label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))
      (dj :=
        (mandatoryFrame before formula).distinctVariables.toArray)
      hpoint
    simpa [SourceFrame.toRuntime, mandatoryFrame] using this
  · have := frameFloatVarsUnique?_of_pointwise
      (db := insertObj db₀ label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))
      (dj :=
        (mandatoryFrame before formula).distinctVariables.toArray)
      hpoint huniq
    simpa [SourceFrame.toRuntime, mandatoryFrame] using this

set_option maxHeartbeats 2000000 in
/-- **Assert-lane discharge**: the shipped insertion projects to the
canonical after-view, with no supplied projection. -/
theorem projectSourcePrefix?_insert_assert {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (inserted : insertAssertion? before label formula = some after)
    (pos : Pos) :
    projectSourcePrefix?
        (db.insert pos label
          (.assert formula.toRuntime
            (mandatoryFrame before formula).toRuntime)) =
      some (runtimePrefix after).toProjection := by
  have hins := insert_assert_eq_insertObj agreement inserted pos
  rw [hins]
  have hfresh : db.find? label = none :=
    fresh_of_sourceInsert agreement inserted
  have hfreshP : (projectionDB db).find? label = none := hfresh
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, hyps₀, hhyps, h7, asserts₀,
    hasserts, -, hrec⟩ := projectPrefix?_ok_inv hproj
  show projectPrefix?
    (insertObj (projectionDB db) label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label)) = _
  obtain ⟨pre, post, hsplitB, hsplitA, hpreB⟩ :=
    objectEntries_insert_fresh (db := projectionDB db)
      (l := label)
      (obj := .assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label) hfreshP
  have hafter := insertAssertion?_eq_some_state inserted
  have hpoint := mandatory_pointwise_inserted_pdb
    (obj := .assert formula.toRuntime
      (mandatoryFrame before formula).toRuntime label)
    (formula := formula) agreement hfresh
  -- guards
  have h1' : (insertObj (projectionDB db) label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime
        label)).error?.isNone = true := h1
  have hnew := newAssert_wellFormedObj_of_pointwise
    (db₀ := projectionDB db) inserted hpoint
  have h2' := wellFormed?_insertObj hfreshP h2 hnew
  have hdvnew : (insertObj (projectionDB db) label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime
        label)).frameDvVarsInFrame?
      (mandatoryFrame before formula).toRuntime = true := by
    have hvalidNew := newAssert_valid inserted
    simp only [sourceAssertionValid, Bool.and_eq_true] at hvalidNew
    obtain ⟨⟨⟨hfv, -⟩, -⟩, -⟩ := hvalidNew
    have hsfv : sourceFrameValid (mandatoryFrame before formula)
        (mandatoryHypotheses before formula) = true := hfv
    simp only [sourceFrameValid, Bool.and_eq_true] at hsfv
    exact frameDvVars_of_pointwise hpoint (by
      simpa [sourceFrameDVValid_eq_runtime] using hsfv.2)
  have h3' := assertDvVarsInFrame?_insertObj
    (obj := .assert formula.toRuntime
      (mandatoryFrame before formula).toRuntime label) hfreshP
    (by
      rw [DB.wellFormed?, Bool.and_eq_true] at h2
      exact h2.2) h3 hdvnew
  have h4' : rawCallerDVStrict
      (insertObj (projectionDB db) label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label)) =
      true := by
    rw [rawCallerDVStrict_insertObj]
    exact h4
  -- entries facts
  have hembNew : objectEmbeddedNameMatches label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label) = true := by
    simp [objectEmbeddedNameMatches]
  have h5' : ((objectEntries
      (insertObj (projectionDB db) label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))).all
      fun e => objectEmbeddedNameMatches e.1 e.2) = true := by
    have h5B := h5
    rw [hsplitB, List.all_eq_true] at h5B
    rw [hsplitA, List.all_eq_true]
    intro e he
    rcases List.mem_append.mp he with hp | hrest
    · exact h5B e (List.mem_append_left _ hp)
    · rcases List.mem_cons.mp hrest with rfl | hp
      · exact hembNew
      · exact h5B e (List.mem_append_right _ hp)
  -- field values before/after
  have hdcB : declaredConstantNames (objectEntries (projectionDB db))
      = sortStrings before.declaredConstants := by
    have := congrArg PrefixProjection.declaredConstants hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  have hdvB : declaredVariableNames (objectEntries (projectionDB db))
      = sortStrings before.declaredVariables := by
    have := congrArg PrefixProjection.declaredVariables hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  have hcfB : proofFacingCallerFrame (projectionDB db) =
      before.callerFrame.toRuntime := by
    have := congrArg PrefixProjection.callerFrame hrec
    simpa [SourcePrefix.toProjection, runtimePrefix,
      SourceFrame.toRuntime] using this.symm
  have hhypsB : hyps₀ = before.activeHypotheses := by
    have := congrArg PrefixProjection.activeHypotheses hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  have hasB : asserts₀ =
      (sortSourceAssertions before.assertions).map
        SourceAssertion.toProjectionView := by
    have := congrArg PrefixProjection.assertions hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  -- inserted-entry field evolutions
  have hdcA : declaredConstantNames
      (objectEntries (insertObj (projectionDB db) label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))) =
      declaredConstantNames (objectEntries (projectionDB db)) := by
    rw [hsplitA, hsplitB, declaredConstantNames_append,
      declaredConstantNames_append,
      declaredConstantNames_cons_assert]
  have hdvA : declaredVariableNames
      (objectEntries (insertObj (projectionDB db) label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))) =
      declaredVariableNames (objectEntries (projectionDB db)) := by
    rw [hsplitA, hsplitB, declaredVariableNames_append,
      declaredVariableNames_append,
      declaredVariableNames_cons_assert]
  have h6' : ((declaredConstantNames
      (objectEntries (insertObj (projectionDB db) label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label)))).all
      fun c => !((declaredVariableNames
        (objectEntries (insertObj (projectionDB db) label
          (.assert formula.toRuntime
            (mandatoryFrame before formula).toRuntime
            label)))).contains c)) = true := by
    rw [hdcA, hdvA]
    exact h6
  -- hypotheses and caller frame stability
  have hresolve : ∀ lbl ∈ (projectionDB db).frame.hyps.toList,
      (projectionDB db).find? lbl ≠ none :=
    projectHypotheses?_resolves hhyps
  have hhyps' : projectHypotheses?
      (insertObj (projectionDB db) label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))
      (projectionDB db).frame.hyps.toList = some hyps₀ := by
    rw [projectHypotheses?_congr (db := projectionDB db)
      (fun lbl hlbl =>
        find?_insertObj_occupied hfreshP (hresolve lbl hlbl))]
    exact hhyps
  have hcf' : proofFacingCallerFrame
      (insertObj (projectionDB db) label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label)) =
      proofFacingCallerFrame (projectionDB db) :=
    proofFacingCallerFrame_insertObj hfreshP hresolve
  have h7' : frameProjectionValid
      (proofFacingCallerFrame
        (insertObj (projectionDB db) label
          (.assert formula.toRuntime
            (mandatoryFrame before formula).toRuntime label)))
      hyps₀ = true := by
    rw [hcf']
    exact h7
  -- assertions: stability, the new view, and canonical alignment
  have hassertsSplit : projectAssertionsFromEntries?
      (projectionDB db) (pre ++ post) = some asserts₀ :=
    hsplitB ▸ hasserts
  have hres := projectAssertionsFromEntries?_resolves
    (db := projectionDB db) hassertsSplit
  obtain ⟨vpre, vpost, hvpre, hvpost, hcat⟩ :=
    projectAssertionsFromEntries?_split_inv (db := projectionDB db)
      hassertsSplit
  have hvpre' := projectAssertionsFromEntries?_congr
    (db := projectionDB db)
    (db' := insertObj (projectionDB db) label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label))
    hvpre
    (fun e he f fr emb hshape lbl hlbl =>
      find?_insertObj_occupied hfreshP
        (hres e (List.mem_append_left _ he) f fr emb hshape lbl hlbl))
  have hvpost' := projectAssertionsFromEntries?_congr
    (db := projectionDB db)
    (db' := insertObj (projectionDB db) label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label))
    hvpost
    (fun e he f fr emb hshape lbl hlbl =>
      find?_insertObj_occupied hfreshP
        (hres e (List.mem_append_right _ he) f fr emb hshape lbl
          hlbl))
  have hnewview := projectAssertion?_new
    (db := insertObj (projectionDB db) label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label))
    hpoint (newAssert_valid inserted)
  have hcollA : projectAssertionsFromEntries?
      (insertObj (projectionDB db) label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))
      (objectEntries (insertObj (projectionDB db) label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))) =
      some (vpre ++
        (sourceAssertion before label formula).toProjectionView ::
          vpost) := by
    rw [hsplitA]
    exact projectAssertionsFromEntries?_append hvpre'
      (projectAssertionsFromEntries?_cons_assert hnewview hvpost')
  -- canonical split of the source assertions
  have hvalidBefore := insertAssertion?_valid_before inserted
  have hlabelsNodup : before.assertions.Pairwise
      (fun x y => x.label ≠ y.label) := by
    have hpv := sourcePrefixValid_of_sourceStateValid before
      hvalidBefore
    simp only [sourcePrefixValid, Bool.and_eq_true] at hpv
    have hrl := hpv.2
    simp only [sourceRuleLabelsValid, Bool.and_eq_true] at hrl
    have hnodup : (sourcePrefixRuleLabels
        before.toSourcePrefix).Nodup :=
      nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp hrl.2)
    have hmapNodup : (before.assertions.map
        SourceAssertion.label).Nodup := by
      unfold sourcePrefixRuleLabels at hnodup
      exact (List.nodup_append.mp (by
        simpa [SourceState.toSourcePrefix] using hnodup)).2.1
    exact List.pairwise_map.mp hmapNodup
  have hfreshLabels : ∀ x ∈ before.assertions,
      (sourceAssertion before label formula).label ≠ x.label := by
    have hnotin := insertAssertion?_label_fresh inserted
    intro x hx heq
    apply hnotin
    have hv := hvalidBefore
    simp only [sourceStateValid, Bool.and_eq_true] at hv
    have hall := hv.1.1.1.2
    rw [List.all_eq_true] at hall
    have hxl := hall x.label (List.mem_map_of_mem hx)
    unfold SourceState.objectNames
    have : (sourceAssertion before label formula).label = label := rfl
    rw [this] at heq
    rw [heq]
    exact List.mem_append_right _ (List.mem_of_elem_eq_true hxl)
  obtain ⟨spre, spost, hsB, hsA, hsBound⟩ :=
    sortSourceAssertions_append_fresh hlabelsNodup hfreshLabels
  -- both splits are the ≤-boundary split of the same sorted list
  have hcatMap : (spre.map SourceAssertion.toProjectionView) ++
      (spost.map SourceAssertion.toProjectionView) =
      vpre ++ vpost := by
    rw [← List.map_append, ← hsB, ← hasB]
    exact hcat
  have hsorted := List.pairwise_mergeSort
    (le := fun (a b : String × Metamath.Verify.Object) =>
      a.1 ≤ b.1)
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at *
      exact le_trans hab hbc)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total a.1 b.1)
    ((projectionDB db).objects.insert label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label)).toList
  have hsortedA : (pre ++ (label,
      (Metamath.Verify.Object.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime label)) ::
        post).Pairwise
      (fun a b => (decide (a.1 ≤ b.1) : Bool) = true) := by
    rw [← hsplitA]
    exact hsorted
  have hpostGe : ∀ e ∈ post, label ≤ e.1 := by
    have hmid := (List.pairwise_append.mp hsortedA).2.1
    intro e he
    have := (List.pairwise_cons.mp hmid).1 e he
    simpa using this
  have hsortedS := List.pairwise_mergeSort
    (le := fun (a b : SourceAssertion) => a.label ≤ b.label)
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at *
      exact le_trans hab hbc)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total a.label b.label)
    (before.assertions ++ [sourceAssertion before label formula])
  have hsortedSA : (spre ++
      sourceAssertion before label formula :: spost).Pairwise
      (fun a b => (decide (a.label ≤ b.label) : Bool) = true) := by
    rw [← hsA]
    exact hsortedS
  have hspostGe : ∀ x ∈ spost, label ≤ x.label := by
    have hmid := (List.pairwise_append.mp hsortedSA).2.1
    intro x hx
    have := (List.pairwise_cons.mp hmid).1 x hx
    exact of_decide_eq_true this
  have hvpreLabels := projectAssertionsFromEntries?_labels
    (db := projectionDB db) hvpre
  have hvpostLabels := projectAssertionsFromEntries?_labels
    (db := projectionDB db) hvpost
  have hvpreBound : ∀ v ∈ vpre, ¬(label ≤ v.label) := by
    intro v hv
    have hvl : v.label ∈ pre.filterMap fun e =>
        match e.2 with
        | .assert _ _ _ => some e.1
        | _ => none := by
      rw [← hvpreLabels]
      exact List.mem_map_of_mem hv
    obtain ⟨e, he, hkey⟩ := List.mem_filterMap.mp hvl
    have hbound := hpreB e he
    obtain ⟨ekey, eobj⟩ := e
    cases eobj with
    | assert f fr emb =>
        cases Option.some.inj hkey
        simpa using hbound
    | const c => exact nomatch hkey
    | var vn => exact nomatch hkey
    | hyp ess f emb => exact nomatch hkey
  have hvpostBound : ∀ v ∈ vpost, label ≤ v.label := by
    intro v hv
    have hvl : v.label ∈ post.filterMap fun e =>
        match e.2 with
        | .assert _ _ _ => some e.1
        | _ => none := by
      rw [← hvpostLabels]
      exact List.mem_map_of_mem hv
    obtain ⟨e, he, hkey⟩ := List.mem_filterMap.mp hvl
    have hge := hpostGe e he
    obtain ⟨ekey, eobj⟩ := e
    cases eobj with
    | assert f fr emb =>
        cases Option.some.inj hkey
        exact hge
    | const c => exact nomatch hkey
    | var vn => exact nomatch hkey
    | hyp ess f emb => exact nomatch hkey
  obtain ⟨hpeq, hqeq⟩ := split_unique
    (P := fun v : AssertionView => ¬(label ≤ v.label)) hcatMap
    (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      have := hsBound x hx
      simpa [SourceAssertion.toProjectionView, sourceAssertion]
        using this)
    (fun v hv hcontra => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact hcontra (by
        simpa [SourceAssertion.toProjectionView] using hspostGe x hx))
    hvpreBound
    (fun v hv hcontra => hcontra (hvpostBound v hv))
  -- assemble the collector value against the canonical after-list
  have hcollTarget : vpre ++
      (sourceAssertion before label formula).toProjectionView ::
        vpost =
      (sortSourceAssertions after.assertions).map
        SourceAssertion.toProjectionView := by
    rw [hafter]
    show _ = (sortSourceAssertions
      (before.assertions ++ [sourceAssertion before label formula])).map
        SourceAssertion.toProjectionView
    rw [hsA, List.map_append, List.map_cons, ← hpeq, ← hqeq]
  -- final validity guard and closure
  have hvalidAfter := insertAssertion?_valid inserted
  have h8' := prefixProjectionValid_runtimePrefix hvalidAfter
  have hfinal := projectPrefix?_eq_some_of h1' h2' h3' h4' h5' h6'
    hhyps' h7' hcollA (by
      rw [hcollTarget, hdcA, hdvA, hcf', hdcB, hdvB, hcfB, hhypsB]
      simpa [runtimePrefix, SourcePrefix.toProjection,
        SourceFrame.toRuntime, hafter, SourceState.callerFrame,
        SourceState.proofDistinctVariables,
        SourceState.activeFloatingVariables] using h8')
  rw [hfinal]
  congr 1
  rw [hcollTarget, hdcA, hdvA, hcf', hdcB, hdvB, hcfB, hhypsB]
  simp [runtimePrefix, SourcePrefix.toProjection,
    SourceFrame.toRuntime, hafter, SourceState.callerFrame,
    SourceState.proofDistinctVariables,
    SourceState.activeFloatingVariables]

/-- **Premise-free agreement preservation for `$a`/`$p` insertion**:
the shipped insertion preserves complete source/runtime agreement with
no supplied projection. -/
theorem RuntimeDBAgrees.insertAssertion {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (inserted : insertAssertion? before label formula = some after)
    (pos : Pos) :
    RuntimeDBAgrees
      (db.insert pos label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime))
      after :=
  RuntimeDBAgrees.insertAssertion_of_projection agreement inserted pos
    (projectSourcePrefix?_insert_assert agreement inserted pos)

end AssertLane

/-! ## Scope-pop discharge helpers -/

section PopLane

open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity

private theorem frame_shrink_dj (fr : RuntimeFrame) (p : Nat × Nat) :
    (fr.shrink p).dj = fr.dj.shrink p.1 := rfl

private theorem frame_shrink_hyps (fr : RuntimeFrame) (p : Nat × Nat) :
    (fr.shrink p).hyps = fr.hyps.shrink p.2 := rfl

private theorem runtimeSize_fst (boundary : ScopeBoundary) :
    (ScopeBoundary.runtimeSize boundary).1 =
      boundary.activeDistinctLength := rfl

private theorem runtimeSize_snd (boundary : ScopeBoundary) :
    (ScopeBoundary.runtimeSize boundary).2 =
      boundary.activeHypothesisLength := rfl

theorem projectHypotheses?_take {db : RuntimeDB} :
    ∀ {labels : List String} {views : List HypothesisView} (n : Nat),
      projectHypotheses? db labels = some views →
      projectHypotheses? db (labels.take n) = some (views.take n) := by
  intro labels
  induction labels with
  | nil =>
      intro views n h
      cases Option.some.inj h
      simp [projectHypotheses?]
  | cons l rest ih =>
      intro views n h
      unfold projectHypotheses? at h
      rw [List.mapM_cons] at h
      obtain ⟨v, hv, h⟩ := bind_some_inv h
      obtain ⟨vs, hvs, h⟩ := bind_some_inv h
      cases Option.some.inj h
      cases n with
      | zero => simp [projectHypotheses?]
      | succ m =>
          have htail := ih m hvs
          unfold projectHypotheses? at htail ⊢
          simp only [List.take_succ_cons, List.mapM_cons, hv, htail]
          rfl

/-- Generalized float-variable computation: any frame whose hypothesis
labels are the views' labels. -/
theorem frameFloatVars_of_pointwise' {db : RuntimeDB}
    {hyps : List HypothesisView} {fr : RuntimeFrame}
    (hlist : fr.hyps.toList = hyps.map HypothesisView.label)
    (hpoint : ∀ hyp ∈ hyps,
      projectHypothesis? db hyp.label = some hyp) :
    db.frameFloatVars fr = floatingVariableNames hyps := by
  unfold DB.frameFloatVars floatingVariableNames
  rw [hlist, List.filterMap_map]
  apply List.filterMap_congr
  intro hyp hh
  obtain ⟨rf, hfind, hform, -⟩ :=
    projectHypothesis?_eq_some_fidelity db hyp.label hyp
      (hpoint hyp hh)
  simp only [Function.comp_apply]
  rw [hfind]
  cases hyp with
  | essential lbl f =>
      simp [hypothesisEssentialBit, HypothesisView.floatingVariable?]
  | floating lbl typecode variableName =>
      simp only [hypothesisEssentialBit]
      have hrf : rf = (⟨typecode, [.var variableName]⟩ :
          ConstantHeadedFormula).toRuntime :=
        (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
          simpa [HypothesisView.formula] using hform)
      subst hrf
      simp [ConstantHeadedFormula.toRuntime, Formula.isFloatShape,
        HypothesisView.floatingVariable?]

/-- Frame hypothesis checks, membership-based. -/
theorem frameHypsOk?_of_pointwise' {db : RuntimeDB}
    {hyps : List HypothesisView} {fr : RuntimeFrame}
    (hlist : fr.hyps.toList = hyps.map HypothesisView.label)
    (hpoint : ∀ hyp ∈ hyps,
      projectHypothesis? db hyp.label = some hyp) :
    db.frameHypsOk? fr = true := by
  rw [DB.frameHypsOk?, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  have hmem : fr.hyps[i]! ∈ fr.hyps.toList := by
    rw [getElem!_pos fr.hyps i hi]
    exact Array.getElem_mem_toList hi
  rw [hlist] at hmem
  obtain ⟨hyp, hh, hlab⟩ := List.mem_map.mp hmem
  rw [← hlab]
  exact hypOK?_of_pointwise (hpoint hyp hh)

/-- Frame float-variable uniqueness, generalized. -/
theorem frameFloatVarsUnique?_of_pointwise' {db : RuntimeDB}
    {hyps : List HypothesisView} {fr : RuntimeFrame}
    (hlist : fr.hyps.toList = hyps.map HypothesisView.label)
    (hpoint : ∀ hyp ∈ hyps,
      projectHypothesis? db hyp.label = some hyp)
    (huniq : hasUniqueFloatingVariables hyps = true) :
    db.frameFloatVarsUnique? fr = true := by
  have hnodup :
      (hyps.filterMap HypothesisView.floatingVariable?).Nodup := by
    apply nodup_of_eraseDups_length_eq
    have := huniq
    simp only [hasUniqueFloatingVariables, floatingVariableNames,
      beq_iff_eq] at this
    exact this
  have hpairGet := List.pairwise_iff_getElem.mp
    (pairwise_of_nodup_filterMap hnodup)
  have hsize : fr.hyps.size = hyps.length := by
    rw [← fr.hyps.length_toList, hlist, List.length_map]
  have hbang : ∀ (i : Nat) (hilt : i < hyps.length),
      fr.hyps[i]! = hyps[i].label := by
    intro i hi
    rw [getElem!_pos fr.hyps i (by rw [hsize]; exact hi)]
    have h1 : fr.hyps.toList[i]'(by
        rw [fr.hyps.length_toList, hsize]; exact hi) =
        fr.hyps[i]'(by rw [hsize]; exact hi) :=
      Array.getElem_toList _
    rw [← h1]
    have h2 := congrArg (fun l => l[i]?) hlist
    simp only [List.getElem?_map] at h2
    have h3 : fr.hyps.toList[i]? = some (hyps[i].label) := by
      rw [h2, List.getElem?_eq_getElem hi]
      rfl
    rw [List.getElem?_eq_getElem (by
      rw [fr.hyps.length_toList, hsize]; exact hi)] at h3
    exact Option.some.inj h3
  rw [DB.frameFloatVarsUnique?]
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range, hsize] at hi hj
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, dite_false]
    rw [hbang i hi, hbang j hj]
    have hne : ∀ x y,
        HypothesisView.floatingVariable? hyps[i] = some x →
        HypothesisView.floatingVariable? hyps[j] = some y →
        x ≠ y := by
      rcases Nat.lt_trichotomy i j with hlt | heq | hgt
      · exact hpairGet i j hi hj hlt
      · exact absurd heq hij
      · exact fun x y hx hy heq =>
          hpairGet j i hj hi hgt y x hy hx heq.symm
    obtain ⟨rfi, hfindi, hformi, -⟩ :=
      projectHypothesis?_eq_some_fidelity db hyps[i].label hyps[i]
        (hpoint hyps[i] (List.getElem_mem hi))
    obtain ⟨rfj, hfindj, hformj, -⟩ :=
      projectHypothesis?_eq_some_fidelity db hyps[j].label hyps[j]
        (hpoint hyps[j] (List.getElem_mem hj))
    rw [hfindi, hfindj]
    cases hci : hyps[i] with
    | essential lbl_i f_i =>
        simp [hypothesisEssentialBit]
    | floating lbl_i tc_i v_i =>
        cases hcj : hyps[j] with
        | essential lbl_j f_j =>
            simp [hypothesisEssentialBit]
        | floating lbl_j tc_j v_j =>
            have hrfi : rfi = (⟨tc_i, [.var v_i]⟩ :
                ConstantHeadedFormula).toRuntime := by
              rw [hci] at hformi
              exact (ConstantHeadedFormula.ofRuntime?_eq_some_iff
                _ _).mp (by
                  simpa [HypothesisView.formula] using hformi)
            have hrfj : rfj = (⟨tc_j, [.var v_j]⟩ :
                ConstantHeadedFormula).toRuntime := by
              rw [hcj] at hformj
              exact (ConstantHeadedFormula.ofRuntime?_eq_some_iff
                _ _).mp (by
                  simpa [HypothesisView.formula] using hformj)
            have hvne : v_i ≠ v_j := by
              refine hne v_i v_j ?_ ?_
              · rw [hci]; rfl
              · rw [hcj]; rfl
            subst hrfi hrfj
            simp [hypothesisEssentialBit,
              Formula.floatVarsDistinct?, Formula.floatVarName,
              ConstantHeadedFormula.toRuntime, hvne]

set_option maxHeartbeats 2000000 in
/-- **Scope-pop discharge**: the shipped pop projects to the canonical
after-view, with no supplied projection. -/
theorem projectSourcePrefix?_popScope {db : RuntimeDB}
    {before after : SourceState}
    (agreement : RuntimeDBAgrees db before) (pos : Pos)
    (closed : closeScope? before = some after) :
    projectSourcePrefix? (db.popScope pos) =
      some (runtimePrefix after).toProjection := by
  obtain ⟨boundary, rest, hscopes, hafter⟩ :=
    closeScope?_eq_some_shape closed
  have hback := agreement.backScope_eq hscopes
  have popEq : db.popScope pos =
      { db with
        frame := db.frame.shrink (ScopeBoundary.runtimeSize boundary)
        scopes := db.scopes.pop } := by
    simp [Metamath.Verify.DB.popScope, hback]
  rw [popEq]
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, hyps₀, hhyps, h7, asserts₀,
    hasserts, -, hrec⟩ := projectPrefix?_ok_inv hproj
  have hhypsB : hyps₀ = before.activeHypotheses := by
    have := congrArg PrefixProjection.activeHypotheses hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  subst hhypsB
  -- the popped projection database, with only the frame changed
  show projectPrefix?
    { projectionDB db with
      frame := db.frame.shrink (ScopeBoundary.runtimeSize boundary) }
    = _
  -- frame-side alignments
  have hlabels : (db.frame.shrink
      (ScopeBoundary.runtimeSize boundary)).hyps.toList =
      after.activeHypotheses.map HypothesisView.label := by
    rw [frame_shrink_hyps, runtimeSize_snd, Array.toList_shrink,
      agreement.rawFrame.2, hafter]
    exact List.map_take.symm
  have hpointAfter : ∀ hyp ∈ after.activeHypotheses,
      projectHypothesis? (projectionDB db) hyp.label = some hyp := by
    intro hyp hh
    refine activeHyp_project_self_pdb agreement hyp ?_
    rw [hafter] at hh
    exact List.mem_of_mem_take hh
  have hpointAfter' : ∀ hyp ∈ after.activeHypotheses,
      projectHypothesis?
        { projectionDB db with
          frame := db.frame.shrink
            (ScopeBoundary.runtimeSize boundary) } hyp.label =
        some hyp := fun hyp hh => hpointAfter hyp hh
  -- guards
  have h2' : ({ projectionDB db with
      frame := db.frame.shrink
        (ScopeBoundary.runtimeSize boundary) } :
        RuntimeDB).wellFormed? = true := by
    rw [DB.wellFormed?, Bool.and_eq_true]
    constructor
    · rw [DB.wellFormedFrame?, Bool.and_eq_true]
      have huniqAfter : hasUniqueFloatingVariables
          after.activeHypotheses = true := by
        have hvalidAfter := applyLocalPayload?_valid
          (payload := .closeScope) closed
        have hpv := sourcePrefixValid_of_sourceStateValid after
          hvalidAfter
        simp only [sourcePrefixValid, Bool.and_eq_true] at hpv
        have hfv := hpv.1.1.1.2
        rw [sourceFrameValid] at hfv
        simp only [Bool.and_eq_true] at hfv
        exact hfv.1.1.1.1.2
      exact ⟨frameHypsOk?_of_pointwise' hlabels hpointAfter',
        frameFloatVarsUnique?_of_pointwise' hlabels hpointAfter'
          huniqAfter⟩
    · have hwfo : (projectionDB db).wellFormedObjects? = true := by
        have hh := h2
        rw [DB.wellFormed?, Bool.and_eq_true] at hh
        exact hh.2
      exact hwfo
  have h3' : ({ projectionDB db with
      frame := db.frame.shrink
        (ScopeBoundary.runtimeSize boundary) } :
        RuntimeDB).assertDvVarsInFrame? = true := h3
  have h4' : rawCallerDVStrict
      ({ projectionDB db with
        frame := db.frame.shrink
          (ScopeBoundary.runtimeSize boundary) } : RuntimeDB) =
      true := by
    rw [rawCallerDVStrict, List.all_eq_true]
    intro pair hpair
    have hmem : pair ∈ (projectionDB db).frame.dj.toList := by
      have : pair ∈ (db.frame.dj.shrink
          boundary.activeDistinctLength).toList := hpair
      rw [Array.toList_shrink] at this
      exact List.mem_of_mem_take this
    rw [rawCallerDVStrict, List.all_eq_true] at h4
    exact h4 pair hmem
  -- hypotheses value
  have hhyps' : projectHypotheses?
      ({ projectionDB db with
        frame := db.frame.shrink
          (ScopeBoundary.runtimeSize boundary) } : RuntimeDB)
      (db.frame.shrink
        (ScopeBoundary.runtimeSize boundary)).hyps.toList =
      some after.activeHypotheses := by
    show projectHypotheses? (projectionDB db) _ = _
    rw [frame_shrink_hyps, runtimeSize_snd, Array.toList_shrink]
    have htake := projectHypotheses?_take
      boundary.activeHypothesisLength hhyps
    rw [show db.frame.hyps.toList =
        (projectionDB db).frame.hyps.toList from rfl, htake, hafter]
  -- caller frame
  have hfloats : ({ projectionDB db with
      frame := db.frame.shrink
        (ScopeBoundary.runtimeSize boundary) } :
        RuntimeDB).frameFloatVars
      (db.frame.shrink (ScopeBoundary.runtimeSize boundary)) =
      floatingVariableNames after.activeHypotheses :=
    frameFloatVars_of_pointwise' hlabels hpointAfter'
  have hcf' : proofFacingCallerFrame
      ({ projectionDB db with
        frame := db.frame.shrink
          (ScopeBoundary.runtimeSize boundary) } : RuntimeDB) =
      after.callerFrame.toRuntime := by
    unfold proofFacingCallerFrame
    have hXframe : ({ projectionDB db with
        frame := db.frame.shrink
          (ScopeBoundary.runtimeSize boundary) } :
          RuntimeDB).frame =
        db.frame.shrink (ScopeBoundary.runtimeSize boundary) := rfl
    rw [hXframe, hfloats]
    unfold SourceFrame.toRuntime SourceState.callerFrame
    refine congrArg₂ Metamath.Verify.Frame.mk ?_ ?_
    · apply Array.ext'
      rw [frame_shrink_dj, runtimeSize_fst, Array.toList_filter,
        Array.toList_shrink, agreement.rawFrame.1,
        List.toList_toArray]
      unfold SourceState.proofDistinctVariables
        SourceState.activeFloatingVariables
      rw [hafter]
      rfl
    · apply Array.ext'
      rw [frame_shrink_hyps, runtimeSize_snd, Array.toList_shrink,
        agreement.rawFrame.2, List.toList_toArray]
      rw [hafter]
      exact List.map_take.symm
  have h7' : frameProjectionValid
      (proofFacingCallerFrame
        ({ projectionDB db with
          frame := db.frame.shrink
            (ScopeBoundary.runtimeSize boundary) } : RuntimeDB))
      after.activeHypotheses = true := by
    rw [hcf', ← sourceFrameValid_eq_runtime]
    have hvalidAfter := applyLocalPayload?_valid
      (payload := .closeScope) closed
    have hpv := sourcePrefixValid_of_sourceStateValid after
      hvalidAfter
    simp only [sourcePrefixValid, Bool.and_eq_true] at hpv
    exact hpv.1.1.1.2
  -- assertions unchanged
  have hasserts' : projectAssertionsFromEntries?
      ({ projectionDB db with
        frame := db.frame.shrink
          (ScopeBoundary.runtimeSize boundary) } : RuntimeDB)
      (objectEntries ({ projectionDB db with
        frame := db.frame.shrink
          (ScopeBoundary.runtimeSize boundary) } : RuntimeDB)) =
      some asserts₀ := by
    show projectAssertionsFromEntries? _
      (objectEntries (projectionDB db)) = _
    exact projectAssertionsFromEntries?_congr hasserts
      (fun e he f fr emb hshape lbl hlbl => rfl)
  have hfinal := projectPrefix?_eq_some_of (db :=
      { projectionDB db with
        frame := db.frame.shrink
          (ScopeBoundary.runtimeSize boundary) })
    h1 h2' h3' h4' h5 h6 hhyps' h7' hasserts' (by
      have hrecEq : asserts₀ =
          (runtimePrefix after).toProjection.assertions := by
        have hthis : (runtimePrefix before).toProjection.assertions =
            asserts₀ := by
          simpa using congrArg PrefixProjection.assertions hrec
        rw [← hthis]
        have hassertsEq : after.assertions = before.assertions := by
          rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection, hassertsEq]
      rw [hrecEq, hcf']
      have hdc : declaredConstantNames (objectEntries
          ({ projectionDB db with
            frame := db.frame.shrink
              (ScopeBoundary.runtimeSize boundary) } :
              RuntimeDB)) =
          (runtimePrefix after).toProjection.declaredConstants := by
        have hthis : (runtimePrefix before).toProjection.declaredConstants
            = declaredConstantNames (objectEntries (projectionDB db)) := by
          simpa using congrArg PrefixProjection.declaredConstants hrec
        rw [show declaredConstantNames (objectEntries
            ({ projectionDB db with
              frame := db.frame.shrink
                (ScopeBoundary.runtimeSize boundary) } :
                RuntimeDB)) =
            declaredConstantNames (objectEntries (projectionDB db))
          from rfl, ← hthis]
        have hcv : after.declaredConstants = before.declaredConstants
          := by rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection, hcv]
      have hdv : declaredVariableNames (objectEntries
          ({ projectionDB db with
            frame := db.frame.shrink
              (ScopeBoundary.runtimeSize boundary) } :
              RuntimeDB)) =
          (runtimePrefix after).toProjection.declaredVariables := by
        have hthis : (runtimePrefix before).toProjection.declaredVariables
            = declaredVariableNames (objectEntries (projectionDB db)) := by
          simpa using congrArg PrefixProjection.declaredVariables hrec
        rw [show declaredVariableNames (objectEntries
            ({ projectionDB db with
              frame := db.frame.shrink
                (ScopeBoundary.runtimeSize boundary) } :
                RuntimeDB)) =
            declaredVariableNames (objectEntries (projectionDB db))
          from rfl, ← hthis]
        have hvv : after.declaredVariables = before.declaredVariables
          := by rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection, hvv]
      rw [hdc, hdv]
      have hact : after.activeHypotheses =
          (runtimePrefix after).toProjection.activeHypotheses := by
        simp [runtimePrefix, SourcePrefix.toProjection]
      rw [hact]
      have hcfT : after.callerFrame.toRuntime =
          (runtimePrefix after).toProjection.callerFrame := by
        simp [runtimePrefix, SourcePrefix.toProjection,
          SourceFrame.toRuntime]
      rw [hcfT]
      have hvalidAfter := applyLocalPayload?_valid
        (payload := .closeScope) closed
      exact prefixProjectionValid_runtimePrefix hvalidAfter)
  rw [hfinal]
  congr 1
  have hrecEq : asserts₀ =
      (runtimePrefix after).toProjection.assertions := by
    have hthis : (runtimePrefix before).toProjection.assertions =
        asserts₀ := by
      simpa using congrArg PrefixProjection.assertions hrec
    rw [← hthis]
    have hassertsEq : after.assertions = before.assertions := by
      rw [hafter]
    simp [runtimePrefix, SourcePrefix.toProjection, hassertsEq]
  have hdcB : (runtimePrefix before).toProjection.declaredConstants =
      declaredConstantNames (objectEntries (projectionDB db)) := by
    simpa using congrArg PrefixProjection.declaredConstants hrec
  have hdvB : (runtimePrefix before).toProjection.declaredVariables =
      declaredVariableNames (objectEntries (projectionDB db)) := by
    simpa using congrArg PrefixProjection.declaredVariables hrec
  rw [hcf', hrecEq]
  rw [show declaredConstantNames (objectEntries
      ({ projectionDB db with
        frame := db.frame.shrink
          (ScopeBoundary.runtimeSize boundary) } : RuntimeDB)) =
      declaredConstantNames (objectEntries (projectionDB db))
    from rfl, ← hdcB]
  rw [show declaredVariableNames (objectEntries
      ({ projectionDB db with
        frame := db.frame.shrink
          (ScopeBoundary.runtimeSize boundary) } : RuntimeDB)) =
      declaredVariableNames (objectEntries (projectionDB db))
    from rfl, ← hdvB]
  have hc : after.declaredConstants = before.declaredConstants := by
    rw [hafter]
  have hv : after.declaredVariables = before.declaredVariables := by
    rw [hafter]
  simp [runtimePrefix, SourcePrefix.toProjection,
    SourceFrame.toRuntime, hc, hv]

/-- **Premise-free agreement preservation for `$}`**: the shipped pop
preserves complete agreement with no supplied projection. -/
theorem RuntimeDBAgrees.popScope' {db : RuntimeDB}
    {before after : SourceState}
    (agreement : RuntimeDBAgrees db before) (pos : Pos)
    (closed : closeScope? before = some after) :
    RuntimeDBAgrees (db.popScope pos) after :=
  RuntimeDBAgrees.popScope_of_projection agreement pos closed
    (projectSourcePrefix?_popScope agreement pos closed)

end PopLane

/-! ## Hypothesis-insertion lane ingredients -/

section HypLane

open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4

@[simp] theorem declaredConstantNames_cons_hyp
    (l : String) (ess : Bool) (f : Metamath.Verify.Formula)
    (e : String) (rest : List (String × Metamath.Verify.Object)) :
    declaredConstantNames ((l, .hyp ess f e) :: rest) =
      declaredConstantNames rest := rfl

@[simp] theorem declaredVariableNames_cons_hyp
    (l : String) (ess : Bool) (f : Metamath.Verify.Formula)
    (e : String) (rest : List (String × Metamath.Verify.Object)) :
    declaredVariableNames ((l, .hyp ess f e) :: rest) =
      declaredVariableNames rest := rfl

theorem projectHypotheses?_append_singleton {db : RuntimeDB} :
    ∀ {labels : List String} {views : List HypothesisView}
      {l : String} {v : HypothesisView},
      projectHypotheses? db labels = some views →
      projectHypothesis? db l = some v →
      projectHypotheses? db (labels ++ [l]) = some (views ++ [v]) := by
  intro labels
  induction labels with
  | nil =>
      intro views l v h hv
      cases Option.some.inj h
      unfold projectHypotheses?
      simp [List.mapM_cons, hv]
  | cons x rest ih =>
      intro views l v h hv
      unfold projectHypotheses? at h ⊢
      rw [List.mapM_cons] at h
      obtain ⟨vx, hvx, h⟩ := bind_some_inv h
      obtain ⟨vs, hvs, h⟩ := bind_some_inv h
      cases Option.some.inj h
      have htail := ih hvs hv
      unfold projectHypotheses? at htail
      rw [List.cons_append, List.mapM_cons, hvx, htail]
      rfl

/-- The freshly inserted hypothesis object projects to its view. -/
theorem projectHypothesis?_new {db : RuntimeDB}
    {view : HypothesisView} :
    projectHypothesis?
      (insertObj db view.label
        (.hyp (hypothesisEssentialBit view) view.formula.toRuntime
          view.label)) view.label = some view := by
  unfold projectHypothesis?
  rw [show (insertObj db view.label
      (.hyp (hypothesisEssentialBit view) view.formula.toRuntime
        view.label)).find? view.label =
      some (.hyp (hypothesisEssentialBit view)
        view.formula.toRuntime view.label) from
    find?_insertObj_self db view.label _]
  have hform : ConstantHeadedFormula.ofRuntime?
      view.formula.toRuntime = some view.formula :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mpr rfl
  cases view with
  | essential lbl f =>
      simp only [hypothesisEssentialBit, HypothesisView.formula,
        HypothesisView.label] at hform ⊢
      simp [guard, hform]
  | floating lbl typecode variableName =>
      simp only [hypothesisEssentialBit]
      have hform' : ConstantHeadedFormula.ofRuntime?
          ((⟨typecode, [.var variableName]⟩ :
            ConstantHeadedFormula).toRuntime) =
          some ⟨typecode, [.var variableName]⟩ :=
        (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mpr rfl
      simp [guard, HypothesisView.formula, hform',
        HypothesisView.label]

/-- Runtime tail-symbol respect equals the source symbol respect. -/
theorem formulaSymsRespectFrame_bridge {db : RuntimeDB}
    {f : ConstantHeadedFormula} {fr : RuntimeFrame}
    {hyps : List HypothesisView}
    (hfloats : db.frameFloatVars fr = floatingVariableNames hyps) :
    DB.formulaSymsRespectFrame db f.toRuntime fr =
      formulaSymbolsRespectFrame (floatingVariableNames hyps) f := by
  unfold DB.formulaSymsRespectFrame formulaSymbolsRespectFrame
  rw [hfloats]
  have htail : (f.toRuntime.toList).tail = f.body := by
    simp [ConstantHeadedFormula.toRuntime]
  rw [htail]
  apply all_congr_fun
  intro sym _
  cases sym with
  | var v => simp [symbolRespectsFrame]
  | const c => simp [symbolRespectsFrame]

/-- The new hypothesis object's own check (database-independent). -/
theorem newHyp_wellFormedObj (db₀ : RuntimeDB)
    (view : HypothesisView) :
    db₀.wellFormedObj? view.label
      (.hyp (hypothesisEssentialBit view) view.formula.toRuntime
        view.label) = true := by
  cases view with
  | essential lbl f =>
      simp only [DB.wellFormedObj?, hypothesisEssentialBit,
        HypothesisView.formula, if_true]
      exact toRuntime_hasConstHead f
  | floating lbl typecode variableName =>
      simp [DB.wellFormedObj?, hypothesisEssentialBit,
        HypothesisView.formula, ConstantHeadedFormula.toRuntime,
        Formula.isFloatShape]

set_option maxHeartbeats 4000000 in
/-- **Hypothesis-lane discharge**: the shipped hyp insertion plus
frame push projects to the canonical after-view. -/
theorem projectSourcePrefix?_insertHyp {db : RuntimeDB}
    {before after : SourceState} {view : HypothesisView}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? view.label = none)
    (hafter : after =
      { before with
        usedLabels := before.usedLabels ++ [view.label]
        activeHypotheses := before.activeHypotheses ++ [view] })
    (hvalid : sourceStateValid after = true) :
    projectSourcePrefix?
        ({ insertObj db view.label
            (.hyp (hypothesisEssentialBit view)
              view.formula.toRuntime view.label) with
          frame := ⟨db.frame.dj,
            db.frame.hyps.push view.label⟩ } : RuntimeDB) =
      some (runtimePrefix after).toProjection := by
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, hyps₀, hhyps, h7, asserts₀,
    hasserts, -, hrec⟩ := projectPrefix?_ok_inv hproj
  have hhypsB : hyps₀ = before.activeHypotheses := by
    have := congrArg PrefixProjection.activeHypotheses hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  subst hhypsB
  have hfreshP : (projectionDB db).find? view.label = none := hfresh
  show projectPrefix?
    ({ insertObj (projectionDB db) view.label
        (.hyp (hypothesisEssentialBit view)
          view.formula.toRuntime view.label) with
      frame := ⟨db.frame.dj,
        db.frame.hyps.push view.label⟩ } : RuntimeDB) = _
  set dbH : RuntimeDB :=
    { insertObj (projectionDB db) view.label
        (.hyp (hypothesisEssentialBit view)
          view.formula.toRuntime view.label) with
      frame := ⟨db.frame.dj, db.frame.hyps.push view.label⟩ }
    with hdbH
  have hfindH : ∀ l, dbH.find? l =
      (insertObj (projectionDB db) view.label
        (.hyp (hypothesisEssentialBit view)
          view.formula.toRuntime view.label)).find? l :=
    fun _ => rfl
  have hpointOld : ∀ hyp ∈ before.activeHypotheses,
      projectHypothesis? dbH hyp.label = some hyp := by
    intro hyp hh
    have hself := activeHyp_project_self_pdb agreement hyp hh
    have hres := projectHypothesis?_resolves hself
    rw [projectHypothesis?_congr (db := projectionDB db)
      (db' := dbH)
      (by rw [hfindH]; exact find?_insertObj_occupied hfreshP hres)]
    exact hself
  have hpointNew : projectHypothesis? dbH view.label = some view := by
    have hbase := projectHypothesis?_new (db := projectionDB db)
      (view := view)
    rw [projectHypothesis?_congr
      (db := insertObj (projectionDB db) view.label
        (.hyp (hypothesisEssentialBit view)
          view.formula.toRuntime view.label))
      (db' := dbH) (hfindH view.label)]
    exact hbase
  have hpointAll : ∀ hyp ∈ before.activeHypotheses ++ [view],
      projectHypothesis? dbH hyp.label = some hyp := by
    intro hyp hh
    rcases List.mem_append.mp hh with hold | hnew
    · exact hpointOld hyp hold
    · rcases List.mem_singleton.mp hnew with rfl
      exact hpointNew
  have hlabels : dbH.frame.hyps.toList =
      (before.activeHypotheses ++ [view]).map
        HypothesisView.label := by
    show (db.frame.hyps.push view.label).toList = _
    rw [Array.toList_push, agreement.rawFrame.2, List.map_append]
    rfl
  have hwfo : (projectionDB db).wellFormedObjects? = true := by
    have hh := h2
    rw [DB.wellFormed?, Bool.and_eq_true] at hh
    exact hh.2
  have h2' : dbH.wellFormed? = true := by
    rw [DB.wellFormed?, Bool.and_eq_true]
    constructor
    · rw [DB.wellFormedFrame?, Bool.and_eq_true]
      have huniqAfter : hasUniqueFloatingVariables
          (before.activeHypotheses ++ [view]) = true := by
        have hpv := sourcePrefixValid_of_sourceStateValid after
          hvalid
        simp only [sourcePrefixValid, Bool.and_eq_true] at hpv
        have hfv := hpv.1.1.1.2
        rw [sourceFrameValid] at hfv
        simp only [Bool.and_eq_true] at hfv
        have hres := hfv.1.1.1.1.2
        rw [hafter] at hres
        exact hres
      exact ⟨frameHypsOk?_of_pointwise' hlabels hpointAll,
        frameFloatVarsUnique?_of_pointwise' hlabels hpointAll
          huniqAfter⟩
    · exact wellFormedObjects?_insertObj hfreshP hwfo
        (newHyp_wellFormedObj _ view)
  have h3' : dbH.assertDvVarsInFrame? = true :=
    assertDvVarsInFrame?_insertObj
      (obj := .hyp (hypothesisEssentialBit view)
        view.formula.toRuntime view.label)
      hfreshP hwfo h3 trivial
  have h4' : rawCallerDVStrict dbH = true := by
    show (db.frame.dj.toList.all fun pair =>
      decide (pair.1 < pair.2)) = true
    exact h4
  have h1' : dbH.error?.isNone = true := h1
  obtain ⟨pre, post, hsplitB, hsplitA, hpreB⟩ :=
    objectEntries_insert_fresh (db := projectionDB db)
      (l := view.label)
      (obj := .hyp (hypothesisEssentialBit view)
        view.formula.toRuntime view.label) hfreshP
  have hentH : objectEntries dbH =
      pre ++ (view.label,
        Metamath.Verify.Object.hyp (hypothesisEssentialBit view)
          view.formula.toRuntime view.label) :: post := hsplitA
  have h5' : ((objectEntries dbH).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true := by
    have h5B := h5
    rw [hsplitB, List.all_eq_true] at h5B
    rw [hentH, List.all_eq_true]
    intro e he
    rcases List.mem_append.mp he with hp | hrest
    · exact h5B e (List.mem_append_left _ hp)
    · rcases List.mem_cons.mp hrest with rfl | hp
      · simp [objectEmbeddedNameMatches]
      · exact h5B e (List.mem_append_right _ hp)
  have hdcH : declaredConstantNames (objectEntries dbH) =
      declaredConstantNames (objectEntries (projectionDB db)) := by
    rw [hentH, hsplitB, declaredConstantNames_append,
      declaredConstantNames_append, declaredConstantNames_cons_hyp]
  have hdvH : declaredVariableNames (objectEntries dbH) =
      declaredVariableNames (objectEntries (projectionDB db)) := by
    rw [hentH, hsplitB, declaredVariableNames_append,
      declaredVariableNames_append, declaredVariableNames_cons_hyp]
  have h6' : ((declaredConstantNames (objectEntries dbH)).all
      fun c => !((declaredVariableNames
        (objectEntries dbH)).contains c)) = true := by
    rw [hdcH, hdvH]
    exact h6
  have hhyps' : projectHypotheses? dbH dbH.frame.hyps.toList =
      some (before.activeHypotheses ++ [view]) := by
    rw [hlabels, List.map_append]
    have hold : projectHypotheses? dbH
        (before.activeHypotheses.map HypothesisView.label) =
        some before.activeHypotheses := by
      rw [projectHypotheses?_congr (db := projectionDB db)
        (db' := dbH) (fun lbl hlbl => by
          rw [hfindH]
          refine find?_insertObj_occupied hfreshP ?_
          obtain ⟨hyp, hh, rfl⟩ := List.mem_map.mp hlbl
          exact projectHypothesis?_resolves
            (activeHyp_project_self_pdb agreement hyp hh))]
      rw [← agreement.rawFrame.2]
      exact hhyps
    exact projectHypotheses?_append_singleton hold hpointNew
  have hfloatsH : dbH.frameFloatVars dbH.frame =
      floatingVariableNames (before.activeHypotheses ++ [view]) :=
    frameFloatVars_of_pointwise' hlabels hpointAll
  have hcf' : proofFacingCallerFrame dbH =
      after.callerFrame.toRuntime := by
    unfold proofFacingCallerFrame
    rw [hfloatsH]
    unfold SourceFrame.toRuntime SourceState.callerFrame
    refine congrArg₂ Metamath.Verify.Frame.mk ?_ ?_
    · apply Array.ext'
      rw [Array.toList_filter]
      show (db.frame.dj.toList).filter _ = _
      rw [agreement.rawFrame.1, List.toList_toArray]
      unfold SourceState.proofDistinctVariables
        SourceState.activeFloatingVariables
      rw [hafter]
      rfl
    · apply Array.ext'
      show (db.frame.hyps.push view.label).toList = _
      rw [Array.toList_push, agreement.rawFrame.2,
        List.toList_toArray, hafter]
      simp
  have h7' : frameProjectionValid (proofFacingCallerFrame dbH)
      (before.activeHypotheses ++ [view]) = true := by
    rw [hcf', ← sourceFrameValid_eq_runtime]
    have hact : after.activeHypotheses =
        before.activeHypotheses ++ [view] := by rw [hafter]
    rw [← hact]
    have hpv := sourcePrefixValid_of_sourceStateValid after hvalid
    simp only [sourcePrefixValid, Bool.and_eq_true] at hpv
    exact hpv.1.1.1.2
  have hassertsSplit : projectAssertionsFromEntries?
      (projectionDB db) (pre ++ post) = some asserts₀ :=
    hsplitB ▸ hasserts
  have hres := projectAssertionsFromEntries?_resolves
    (db := projectionDB db) hassertsSplit
  have hstable := projectAssertionsFromEntries?_congr
    (db := projectionDB db) (db' := dbH) hassertsSplit
    (fun e he f fr emb hshape lbl hlbl => by
      rw [hfindH]
      exact find?_insertObj_occupied hfreshP
        (hres e he f fr emb hshape lbl hlbl))
  obtain ⟨vpre, vpost, hvpre, hvpost, hcat⟩ :=
    projectAssertionsFromEntries?_split_inv (db := dbH) hstable
  have hmid : projectAssertionsFromEntries? dbH
      ((view.label,
        Metamath.Verify.Object.hyp (hypothesisEssentialBit view)
          view.formula.toRuntime view.label) :: post) =
      projectAssertionsFromEntries? dbH post :=
    projectAssertionsFromEntries?_skip
      (by intro f fr emb hc; exact nomatch hc)
  have hasserts' : projectAssertionsFromEntries? dbH
      (objectEntries dbH) = some asserts₀ := by
    rw [hentH]
    rw [hcat]
    exact projectAssertionsFromEntries?_append hvpre
      (by rw [hmid]; exact hvpost)
  have hfinal := projectPrefix?_eq_some_of (db := dbH)
    h1' h2' h3' h4' h5' h6' hhyps' h7' hasserts' (by
      have hrecEq : asserts₀ =
          (runtimePrefix after).toProjection.assertions := by
        have hthis : (runtimePrefix before).toProjection.assertions =
            asserts₀ := by
          simpa using congrArg PrefixProjection.assertions hrec
        rw [← hthis]
        have hassertsEq : after.assertions = before.assertions := by
          rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection, hassertsEq]
      have hdc : declaredConstantNames (objectEntries dbH) =
          (runtimePrefix after).toProjection.declaredConstants := by
        have hthis : (runtimePrefix
            before).toProjection.declaredConstants =
            declaredConstantNames (objectEntries (projectionDB db))
            := by
          simpa using congrArg PrefixProjection.declaredConstants
            hrec
        rw [hdcH, ← hthis]
        have hcv : after.declaredConstants = before.declaredConstants
          := by rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection, hcv]
      have hdv : declaredVariableNames (objectEntries dbH) =
          (runtimePrefix after).toProjection.declaredVariables := by
        have hthis : (runtimePrefix
            before).toProjection.declaredVariables =
            declaredVariableNames (objectEntries (projectionDB db))
            := by
          simpa using congrArg PrefixProjection.declaredVariables
            hrec
        rw [hdvH, ← hthis]
        have hvv : after.declaredVariables = before.declaredVariables
          := by rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection, hvv]
      rw [hrecEq, hdc, hdv, hcf']
      have hact : before.activeHypotheses ++ [view] =
          (runtimePrefix after).toProjection.activeHypotheses := by
        rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection]
      rw [hact]
      have hcfT : after.callerFrame.toRuntime =
          (runtimePrefix after).toProjection.callerFrame := by
        simp [runtimePrefix, SourcePrefix.toProjection,
          SourceFrame.toRuntime]
      rw [hcfT]
      exact prefixProjectionValid_runtimePrefix hvalid)
  rw [hfinal]
  congr 1
  have hrecEq : asserts₀ =
      (runtimePrefix after).toProjection.assertions := by
    have hthis : (runtimePrefix before).toProjection.assertions =
        asserts₀ := by
      simpa using congrArg PrefixProjection.assertions hrec
    rw [← hthis]
    have hassertsEq : after.assertions = before.assertions := by
      rw [hafter]
    simp [runtimePrefix, SourcePrefix.toProjection, hassertsEq]
  have hdcB : (runtimePrefix before).toProjection.declaredConstants =
      declaredConstantNames (objectEntries (projectionDB db)) := by
    simpa using congrArg PrefixProjection.declaredConstants hrec
  have hdvB : (runtimePrefix before).toProjection.declaredVariables =
      declaredVariableNames (objectEntries (projectionDB db)) := by
    simpa using congrArg PrefixProjection.declaredVariables hrec
  rw [hcf', hrecEq, hdcH, hdvH, ← hdcB, ← hdvB]
  have hc : after.declaredConstants = before.declaredConstants := by
    rw [hafter]
  have hv : after.declaredVariables = before.declaredVariables := by
    rw [hafter]
  have hactA : before.activeHypotheses ++ [view] =
      after.activeHypotheses := by
    rw [hafter]
  rw [hactA]
  simp [runtimePrefix, SourcePrefix.toProjection,
    SourceFrame.toRuntime, hc, hv]

/-- Namespace agreement after any fresh insertion whose source step
appends exactly the label. -/
theorem runtimeNamespaceAfterInsert' {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {obj : Metamath.Verify.Object}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? label = none)
    (hnames : after.objectNames = before.objectNames ++ [label]) :
    RuntimeObjectNamespaceAgrees (insertObj db label obj) after := by
  refine ⟨?_, ?_⟩
  · show (insertObj db label obj).error? = none
    rw [insertObj_error]
    exact agreement.errorFree
  · intro candidate
    rw [hnames, find?_insertObj]
    by_cases hsame : label = candidate
    · subst hsame
      simp
    · simp only [hsame, if_false]
      constructor
      · intro hocc
        exact List.mem_append_left _
          ((agreement.objectNamespace.occupied_iff candidate).mp hocc)
      · intro hmem
        rcases List.mem_append.mp hmem with hold | hnew
        · exact (agreement.objectNamespace.occupied_iff
            candidate).mpr hold
        · rcases List.mem_singleton.mp hnew with rfl
          exact absurd rfl hsame

/-- **Premise-free agreement preservation for `$f`/`$e`**: the shipped
hypothesis insertion plus frame push preserves complete agreement. -/
theorem RuntimeDBAgrees.insertHyp' {db : RuntimeDB}
    {before after : SourceState} {view : HypothesisView}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? view.label = none)
    (hafter : after =
      { before with
        usedLabels := before.usedLabels ++ [view.label]
        activeHypotheses := before.activeHypotheses ++ [view] })
    (hvalid : sourceStateValid after = true) :
    RuntimeDBAgrees
      ({ insertObj db view.label
          (.hyp (hypothesisEssentialBit view)
            view.formula.toRuntime view.label) with
        frame := ⟨db.frame.dj,
          db.frame.hyps.push view.label⟩ } : RuntimeDB) after := by
  have hnames : after.objectNames =
      before.objectNames ++ [view.label] := by
    rw [hafter]
    show before.declaredConstants ++ before.declaredVariables ++
      (before.usedLabels ++ [view.label]) = _
    rw [SourceState.objectNames]
    simp [List.append_assoc]
  refine
    { projection :=
        projectSourcePrefix?_insertHyp agreement hfresh hafter hvalid
      objectNamespace := ?_
      rawFrame := ⟨?_, ?_⟩
      scopeStack := ?_ }
  · have hbase := runtimeNamespaceAfterInsert'
      (obj := .hyp (hypothesisEssentialBit view)
        view.formula.toRuntime view.label)
      agreement hfresh hnames
    exact ⟨hbase.errorFree, hbase.occupied_iff⟩
  · show db.frame.dj.toList = after.activeDistinctVariables
    rw [agreement.rawFrame.1, hafter]
  · show (db.frame.hyps.push view.label).toList =
      after.activeHypotheses.map HypothesisView.label
    rw [Array.toList_push, agreement.rawFrame.2, hafter,
      List.map_append]
    rfl
  · show db.scopes.toList = runtimeScopeSizes after
    rw [agreement.scopeStack]
    unfold runtimeScopeSizes
    rw [hafter]

end HypLane

/-! ## Distinct-variable lane -/

section DjLane

open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity

/-- The generated pairs at the runtime `DJ` carrier. -/
def allDistinctDJ (names : List String) :
    List Metamath.Verify.DJ :=
  allDistinctPairs names

theorem allDistinctDJ_def (names : List String) :
    allDistinctDJ names = allDistinctPairs names := rfl

set_option maxHeartbeats 2000000 in
/-- **Distinct-variable lane discharge**: appending the generated
pairs to the raw caller frame projects to the canonical after-view. -/
theorem projectSourcePrefix?_declareDisjoint {db : RuntimeDB}
    {before after : SourceState} {names : List String}
    (agreement : RuntimeDBAgrees db before)
    (hdecl : declareDisjoint? before names = some after) :
    projectSourcePrefix?
        ({ db with frame := ⟨db.frame.dj ++
            (allDistinctDJ names).toArray,
          db.frame.hyps⟩ } : RuntimeDB) =
      some (runtimePrefix after).toProjection := by
  have hafter := declareDisjoint?_eq_some_state hdecl
  have hvalid : sourceStateValid after = true :=
    applyLocalPayload?_valid
      (payload := .declareDisjoint names) hdecl
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, hyps₀, hhyps, h7, asserts₀,
    hasserts, -, hrec⟩ := projectPrefix?_ok_inv hproj
  have hhypsB : hyps₀ = before.activeHypotheses := by
    have := congrArg PrefixProjection.activeHypotheses hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  subst hhypsB
  show projectPrefix?
    ({ projectionDB db with frame := ⟨db.frame.dj ++
        (allDistinctDJ names).toArray,
      db.frame.hyps⟩ } : RuntimeDB) = _
  set dbD : RuntimeDB :=
    { projectionDB db with frame := ⟨db.frame.dj ++
        (allDistinctDJ names).toArray, db.frame.hyps⟩ }
    with hdbD
  have hlabels : dbD.frame.hyps.toList =
      before.activeHypotheses.map HypothesisView.label :=
    agreement.rawFrame.2
  have hpoint : ∀ hyp ∈ before.activeHypotheses,
      projectHypothesis? dbD hyp.label = some hyp :=
    fun hyp hh => activeHyp_project_self_pdb agreement hyp hh
  have h1' : dbD.error?.isNone = true := h1
  have h2' : dbD.wellFormed? = true := by
    rw [DB.wellFormed?, Bool.and_eq_true]
    constructor
    · rw [DB.wellFormedFrame?, Bool.and_eq_true]
      have huniq : hasUniqueFloatingVariables
          before.activeHypotheses = true := by
        have hpv := sourcePrefixValid_of_sourceStateValid after
          hvalid
        simp only [sourcePrefixValid, Bool.and_eq_true] at hpv
        have hfv := hpv.1.1.1.2
        rw [sourceFrameValid] at hfv
        simp only [Bool.and_eq_true] at hfv
        have hres := hfv.1.1.1.1.2
        rw [hafter] at hres
        exact hres
      exact ⟨frameHypsOk?_of_pointwise' hlabels hpoint,
        frameFloatVarsUnique?_of_pointwise' hlabels hpoint huniq⟩
    · have hh := h2
      rw [DB.wellFormed?, Bool.and_eq_true] at hh
      exact hh.2
  have h3' : dbD.assertDvVarsInFrame? = true := h3
  have h4' : rawCallerDVStrict dbD = true := by
    rw [rawCallerDVStrict, List.all_eq_true]
    intro pair hpair
    have hpair' : pair ∈ db.frame.dj.toList ++
        allDistinctDJ names := by
      have : dbD.frame.dj.toList = db.frame.dj.toList ++
          allDistinctDJ names := by
        show (db.frame.dj ++
          (allDistinctDJ names).toArray).toList = _
        simp
      rwa [this] at hpair
    rcases List.mem_append.mp hpair' with hold | hnew
    · rw [rawCallerDVStrict, List.all_eq_true] at h4
      exact h4 pair hold
    · have hnodup : names.Nodup := by
        have hd := hdecl
        unfold declareDisjoint? at hd
        obtain ⟨-, hd⟩ := guard_bind_some hd
        obtain ⟨-, hd⟩ := guard_bind_some hd
        obtain ⟨hno, -⟩ := guard_bind_some hd
        exact nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp hno)
      have := allDistinctPairsFrom_strict
        (prior := []) (by simpa using hnodup) pair hnew
      simpa using this
  have h5' : ((objectEntries dbD).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true := h5
  have h6' : ((declaredConstantNames (objectEntries dbD)).all
      fun c => !((declaredVariableNames
        (objectEntries dbD)).contains c)) = true := h6
  have hhyps' : projectHypotheses? dbD dbD.frame.hyps.toList =
      some before.activeHypotheses := hhyps
  have hfloats : dbD.frameFloatVars dbD.frame =
      floatingVariableNames before.activeHypotheses :=
    frameFloatVars_of_pointwise' hlabels hpoint
  have hcf' : proofFacingCallerFrame dbD =
      after.callerFrame.toRuntime := by
    unfold proofFacingCallerFrame
    rw [hfloats]
    unfold SourceFrame.toRuntime SourceState.callerFrame
    refine congrArg₂ Metamath.Verify.Frame.mk ?_ ?_
    · apply Array.ext'
      rw [Array.toList_filter]
      show (db.frame.dj ++
        (allDistinctDJ names).toArray).toList.filter _ = _
      rw [show (db.frame.dj ++
          (allDistinctDJ names).toArray).toList =
          db.frame.dj.toList ++
            allDistinctDJ names
          from by simp,
        agreement.rawFrame.1, List.toList_toArray]
      unfold SourceState.proofDistinctVariables
        SourceState.activeFloatingVariables
      rw [hafter]
      simp [List.filter_append]
      rw [allDistinctDJ_def]
      rfl
    · apply Array.ext'
      rw [agreement.rawFrame.2, List.toList_toArray, hafter]
  have h7' : frameProjectionValid (proofFacingCallerFrame dbD)
      before.activeHypotheses = true := by
    rw [hcf', ← sourceFrameValid_eq_runtime]
    have hact : after.activeHypotheses = before.activeHypotheses :=
      by rw [hafter]
    rw [← hact]
    have hpv := sourcePrefixValid_of_sourceStateValid after hvalid
    simp only [sourcePrefixValid, Bool.and_eq_true] at hpv
    exact hpv.1.1.1.2
  have hasserts' : projectAssertionsFromEntries? dbD
      (objectEntries dbD) = some asserts₀ := by
    show projectAssertionsFromEntries? _
      (objectEntries (projectionDB db)) = _
    exact projectAssertionsFromEntries?_congr hasserts
      (fun e he f fr emb hshape lbl hlbl => rfl)
  have hfinal := projectPrefix?_eq_some_of (db := dbD)
    h1' h2' h3' h4' h5' h6' hhyps' h7' hasserts' (by
      have hrecEq : asserts₀ =
          (runtimePrefix after).toProjection.assertions := by
        have hthis : (runtimePrefix before).toProjection.assertions =
            asserts₀ := by
          simpa using congrArg PrefixProjection.assertions hrec
        rw [← hthis]
        have hassertsEq : after.assertions = before.assertions := by
          rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection, hassertsEq]
      have hdc : declaredConstantNames (objectEntries dbD) =
          (runtimePrefix after).toProjection.declaredConstants := by
        have hthis : (runtimePrefix
            before).toProjection.declaredConstants =
            declaredConstantNames (objectEntries (projectionDB db))
            := by
          simpa using congrArg PrefixProjection.declaredConstants
            hrec
        show declaredConstantNames (objectEntries (projectionDB db))
          = _
        rw [← hthis]
        have hcv : after.declaredConstants =
            before.declaredConstants := by rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection, hcv]
      have hdv : declaredVariableNames (objectEntries dbD) =
          (runtimePrefix after).toProjection.declaredVariables := by
        have hthis : (runtimePrefix
            before).toProjection.declaredVariables =
            declaredVariableNames (objectEntries (projectionDB db))
            := by
          simpa using congrArg PrefixProjection.declaredVariables
            hrec
        show declaredVariableNames (objectEntries (projectionDB db))
          = _
        rw [← hthis]
        have hvv : after.declaredVariables =
            before.declaredVariables := by rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection, hvv]
      rw [hrecEq, hdc, hdv, hcf']
      have hact : before.activeHypotheses =
          (runtimePrefix after).toProjection.activeHypotheses := by
        rw [hafter]
        simp [runtimePrefix, SourcePrefix.toProjection]
      rw [hact]
      have hcfT : after.callerFrame.toRuntime =
          (runtimePrefix after).toProjection.callerFrame := by
        simp [runtimePrefix, SourcePrefix.toProjection,
          SourceFrame.toRuntime]
      rw [hcfT]
      exact prefixProjectionValid_runtimePrefix hvalid)
  rw [hfinal]
  congr 1
  have hrecEq : asserts₀ =
      (runtimePrefix after).toProjection.assertions := by
    have hthis : (runtimePrefix before).toProjection.assertions =
        asserts₀ := by
      simpa using congrArg PrefixProjection.assertions hrec
    rw [← hthis]
    have hassertsEq : after.assertions = before.assertions := by
      rw [hafter]
    simp [runtimePrefix, SourcePrefix.toProjection, hassertsEq]
  have hdcB : (runtimePrefix before).toProjection.declaredConstants =
      declaredConstantNames (objectEntries (projectionDB db)) := by
    simpa using congrArg PrefixProjection.declaredConstants hrec
  have hdvB : (runtimePrefix before).toProjection.declaredVariables =
      declaredVariableNames (objectEntries (projectionDB db)) := by
    simpa using congrArg PrefixProjection.declaredVariables hrec
  have hactA : before.activeHypotheses = after.activeHypotheses := by
    rw [hafter]
  have hobjEq : objectEntries dbD =
      objectEntries (projectionDB db) := by
    show objectEntries (projectionDB db) = _
    rfl
  rw [hobjEq, hcf', hrecEq, ← hdcB, ← hdvB, hactA]
  have hc : after.declaredConstants = before.declaredConstants := by
    rw [hafter]
  have hv : after.declaredVariables = before.declaredVariables := by
    rw [hafter]
  simp [runtimePrefix, SourcePrefix.toProjection,
    SourceFrame.toRuntime, hc, hv]

/-- **Distinct-variable co-evolution**: a successful `$d` declaration
preserves runtime/source agreement when the runtime appends the same
generated pairs to its raw caller frame. -/
theorem RuntimeDBAgrees.declareDisjoint' {db : RuntimeDB}
    {before after : SourceState} {names : List String}
    (agreement : RuntimeDBAgrees db before)
    (hdecl : declareDisjoint? before names = some after) :
    RuntimeDBAgrees
      ({ db with frame := ⟨db.frame.dj ++
          (allDistinctDJ names).toArray,
        db.frame.hyps⟩ } : RuntimeDB) after := by
  have hafter := declareDisjoint?_eq_some_state hdecl
  have hnames : after.objectNames = before.objectNames := by
    rw [hafter]
    rfl
  refine
    { projection :=
        projectSourcePrefix?_declareDisjoint agreement hdecl
      objectNamespace := ?_
      rawFrame := ⟨?_, ?_⟩
      scopeStack := ?_ }
  · refine ⟨agreement.objectNamespace.errorFree, ?_⟩
    intro label
    rw [hnames]
    exact agreement.objectNamespace.occupied_iff label
  · show (db.frame.dj ++ (allDistinctDJ names).toArray).toList =
      after.activeDistinctVariables
    rw [show (db.frame.dj ++ (allDistinctDJ names).toArray).toList =
        db.frame.dj.toList ++ allDistinctDJ names from by simp,
      agreement.rawFrame.1, hafter]
    rfl
  · show db.frame.hyps.toList =
      after.activeHypotheses.map HypothesisView.label
    rw [agreement.rawFrame.2, hafter]
  · show db.scopes.toList = runtimeScopeSizes after
    rw [agreement.scopeStack, hafter]
    rfl

end DjLane

/-! ## Constant/variable lane: the strict-sort characterization

`sortStrings` sorts with the strict comparator `<`, so the stock
`pairwise_mergeSort` (which needs a total comparator) does not apply.
On duplicate-free input the strict and non-strict comparators agree on
every pair the sort actually compares, so the sorts coincide; the
comparator congruence is proved by the merge-sort recursion itself,
using that `merge` only ever compares elements from disjoint halves. -/

section SymLane

open List.MergeSort.Internal
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4

/-- `merge` only compares cross pairs, so comparators that agree on
cross pairs produce identical merges. -/
theorem merge_congr {α : Type _} {r s : α → α → Bool}
    {l l' : List α}
    (h : ∀ a ∈ l, ∀ b ∈ l', r a b = s a b) :
    l.merge l' r = l.merge l' s := by
  have hm := List.map_merge (f := id) (r := r) (s := s)
    (l := l) (l' := l') (by simpa using h)
  simpa using hm

/-- Comparator congruence for `mergeSort` on duplicate-free lists:
only distinct pairs are ever compared. -/
theorem mergeSort_congr_of_nodup {α : Type _}
    {r s : α → α → Bool} :
    ∀ {l : List α}, l.Nodup →
      (∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b = s a b) →
      l.mergeSort r = l.mergeSort s
  | [], _, _ => by simp
  | [a], _, _ => by simp
  | a :: b :: xs, hnd, hrs => by
      have hlen₁ : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length <
          xs.length + 1 + 1 := by
        simp [splitInTwo_fst]; omega
      have hlen₂ : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length <
          xs.length + 1 + 1 := by
        simp [splitInTwo_snd]; omega
      have htake : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1 =
          (a :: b :: xs).take ((xs.length + 1 + 1 + 1) / 2) := by
        simp [splitInTwo_fst]
      have hdrop : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1 =
          (a :: b :: xs).drop ((xs.length + 1 + 1 + 1) / 2) := by
        simp [splitInTwo_snd]
      have hsub₁ : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1 ⊆
          a :: b :: xs := by
        rw [htake]; exact List.take_subset _ _
      have hsub₂ : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1 ⊆
          a :: b :: xs := by
        rw [hdrop]; exact List.drop_subset _ _
      have hnd₁ : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.Nodup := by
        rw [htake]; exact hnd.sublist (List.take_sublist _ _)
      have hnd₂ : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.Nodup := by
        rw [hdrop]; exact hnd.sublist (List.drop_sublist _ _)
      have hdisj : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.Disjoint
          (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1 := by
        rw [htake, hdrop]
        exact List.disjoint_take_drop hnd le_rfl
      rw [List.mergeSort, List.mergeSort]
      rw [mergeSort_congr_of_nodup hnd₁
          (fun x hx y hy hxy => hrs x (hsub₁ hx) y (hsub₁ hy) hxy),
        mergeSort_congr_of_nodup hnd₂
          (fun x hx y hy hxy => hrs x (hsub₂ hx) y (hsub₂ hy) hxy)]
      exact merge_congr (fun x hx y hy =>
        hrs x (hsub₁ (List.mem_mergeSort.mp hx))
          y (hsub₂ (List.mem_mergeSort.mp hy))
          (fun hxy => hdisj (List.mem_mergeSort.mp hx)
            (by rw [hxy]; exact List.mem_mergeSort.mp hy)))
  termination_by l => l.length

/-- On duplicate-free input the strict string sort agrees with the
total `≤` sort. -/
theorem sortStrings_eq_mergeSort_le {l : List String}
    (hnd : l.Nodup) :
    sortStrings l = l.mergeSort (fun a b => a ≤ b) :=
  mergeSort_congr_of_nodup hnd (fun a _ b _ hab => by
    simp only [decide_eq_decide]
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hab⟩)

/-- The strict string sort of a duplicate-free list is strictly
increasing. -/
theorem sortStrings_pairwise_lt {l : List String} (hnd : l.Nodup) :
    (sortStrings l).Pairwise (· < ·) := by
  rw [sortStrings_eq_mergeSort_le hnd]
  have hp := List.pairwise_mergeSort
    (le := fun a b : String => a ≤ b)
    (fun a b c hab hbc => decide_eq_true
      (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (fun a b => by
      simpa [Bool.or_eq_true, decide_eq_true_iff] using le_total a b)
    l
  have hnd' : (l.mergeSort (fun a b : String => a ≤ b)).Nodup :=
    ((List.mergeSort_perm l _).nodup_iff).mpr hnd
  exact (hp.and hnd').imp
    (fun h => lt_of_le_of_ne (of_decide_eq_true h.1) h.2)

@[simp] theorem declaredConstantNames_cons_const
    (l c : String) (rest : List (String × Metamath.Verify.Object)) :
    declaredConstantNames ((l, .const c) :: rest) =
      c :: declaredConstantNames rest := rfl

@[simp] theorem declaredConstantNames_cons_var
    (l v : String) (rest : List (String × Metamath.Verify.Object)) :
    declaredConstantNames ((l, .var v) :: rest) =
      declaredConstantNames rest := rfl

@[simp] theorem declaredVariableNames_cons_const
    (l c : String) (rest : List (String × Metamath.Verify.Object)) :
    declaredVariableNames ((l, .const c) :: rest) =
      declaredVariableNames rest := rfl

@[simp] theorem declaredVariableNames_cons_var
    (l v : String) (rest : List (String × Metamath.Verify.Object)) :
    declaredVariableNames ((l, .var v) :: rest) =
      v :: declaredVariableNames rest := rfl

/-- The label-sorted entry list is strictly increasing on labels. -/
theorem objectEntries_pairwise_lt (db : RuntimeDB) :
    (objectEntries db).Pairwise (fun a b => a.1 < b.1) := by
  have hnodupBeq := Std.HashMap.distinct_keys_toList (m := db.objects)
  have hnodup : db.objects.toList.Pairwise (fun a b => a.1 ≠ b.1) :=
    hnodupBeq.imp (fun h => by simpa using h)
  have htrans : ∀ (a b c : String × Metamath.Verify.Object),
      (decide (a.1 ≤ b.1)) → (decide (b.1 ≤ c.1)) →
        (decide (a.1 ≤ c.1) : Bool) := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    exact le_trans hab hbc
  have htotal : ∀ (a b : String × Metamath.Verify.Object),
      (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1) : Bool) := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total a.1 b.1
  have hs := List.pairwise_mergeSort htrans htotal db.objects.toList
  have hp := List.mergeSort_perm db.objects.toList
    (fun a b => a.1 ≤ b.1)
  have hnodup' : (objectEntries db).Pairwise (fun a b => a.1 ≠ b.1) :=
    (hp.pairwise_iff (fun h heq => h heq.symm)).mpr hnodup
  exact (hs.and hnodup').imp (fun h =>
    lt_of_le_of_ne (by simpa using h.1) h.2)

/-- Fresh insertion prepends the new entry up to permutation. -/
theorem objectEntries_insert_perm {db : RuntimeDB} {l : String}
    {obj : Metamath.Verify.Object} (hfresh : db.find? l = none) :
    (objectEntries (insertObj db l obj)).Perm
      ((l, obj) :: objectEntries db) := by
  have h1 : (objectEntries (insertObj db l obj)).Perm
      (insertObj db l obj).objects.toList :=
    List.mergeSort_perm _ _
  have h3 : db.objects.toList.Perm (objectEntries db) :=
    (List.mergeSort_perm _ _).symm
  exact h1.trans ((toList_insertObj_perm hfresh).trans
    (List.Perm.cons _ h3))

/-- Entries resolve their own labels. -/
theorem find?_of_mem_objectEntries {db : RuntimeDB}
    {entry : String × Metamath.Verify.Object}
    (hmem : entry ∈ objectEntries db) :
    db.find? entry.1 = some entry.2 := by
  have hlist := (mem_objectEntries_iff db entry).mp hmem
  have hkey : db.objects[entry.1]? = some entry.2 :=
    (Std.HashMap.mem_toList_iff_getElem?_eq_some).mp
      (by simpa using hlist)
  exact hkey

/-- Every projected variable name is an occupied runtime label. -/
theorem find?_of_mem_declaredVariableNames {db : RuntimeDB} {v : String}
    (hguard : ((objectEntries db).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true)
    (hv : v ∈ declaredVariableNames (objectEntries db)) :
    db.find? v ≠ none := by
  obtain ⟨entry, hmem, hextract⟩ := List.mem_filterMap.mp hv
  obtain ⟨l, obj⟩ := entry
  cases obj with
  | var w =>
      have hw : w = v := by
        simpa using hextract
      subst hw
      rw [List.all_eq_true] at hguard
      have hlabel : w = l := by
        simpa [objectEmbeddedNameMatches] using
          hguard (l, .var w) hmem
      subst hlabel
      rw [find?_of_mem_objectEntries hmem]
      simp
  | const c => exact nomatch hextract
  | hyp ess f e => exact nomatch hextract
  | assert f fr e => exact nomatch hextract

/-- Every projected constant name is an occupied runtime label. -/
theorem find?_of_mem_declaredConstantNames {db : RuntimeDB} {c : String}
    (hguard : ((objectEntries db).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true)
    (hc : c ∈ declaredConstantNames (objectEntries db)) :
    db.find? c ≠ none := by
  obtain ⟨entry, hmem, hextract⟩ := List.mem_filterMap.mp hc
  obtain ⟨l, obj⟩ := entry
  cases obj with
  | const w =>
      have hw : w = c := by
        simpa using hextract
      subst hw
      rw [List.all_eq_true] at hguard
      have hlabel : w = l := by
        simpa [objectEmbeddedNameMatches] using
          hguard (l, .const w) hmem
      subst hlabel
      rw [find?_of_mem_objectEntries hmem]
      simp
  | var v => exact nomatch hextract
  | hyp ess f e => exact nomatch hextract
  | assert f fr e => exact nomatch hextract

/-- Under the embedded-name guard, extracted constant names inherit
the strict label order. -/
theorem declaredConstantNames_pairwise_lt {db : RuntimeDB}
    (hguard : ((objectEntries db).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true) :
    (declaredConstantNames (objectEntries db)).Pairwise (· < ·) := by
  rw [List.all_eq_true] at hguard
  have hlt := objectEntries_pairwise_lt db
  refine List.pairwise_filterMap.mpr ?_
  refine (List.pairwise_iff_forall_sublist.mpr ?_)
  intro a b hab x hx y hy
  have hmem₁ : a ∈ objectEntries db := hab.subset (by simp)
  have hmem₂ : b ∈ objectEntries db := hab.subset (by simp)
  have hlab : a.1 < b.1 :=
    (List.pairwise_iff_forall_sublist.mp hlt) hab
  obtain ⟨la, oa⟩ := a
  obtain ⟨lb, ob⟩ := b
  cases oa with
  | const ca =>
      cases ob with
      | const cb =>
          have hxa : ca = x := by simpa using hx
          have hyb : cb = y := by simpa using hy
          have hla : ca = la := by
            simpa [objectEmbeddedNameMatches] using
              hguard (la, .const ca) hmem₁
          have hlb : cb = lb := by
            simpa [objectEmbeddedNameMatches] using
              hguard (lb, .const cb) hmem₂
          rw [← hxa, ← hyb, hla, hlb]
          exact hlab
      | var vb => exact nomatch hy
      | hyp ess f e => exact nomatch hy
      | assert f fr e => exact nomatch hy
  | var va => exact nomatch hx
  | hyp ess f e => exact nomatch hx
  | assert f fr e => exact nomatch hx

/-- Under the embedded-name guard, extracted variable names inherit
the strict label order. -/
theorem declaredVariableNames_pairwise_lt {db : RuntimeDB}
    (hguard : ((objectEntries db).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true) :
    (declaredVariableNames (objectEntries db)).Pairwise (· < ·) := by
  rw [List.all_eq_true] at hguard
  have hlt := objectEntries_pairwise_lt db
  refine List.pairwise_filterMap.mpr ?_
  refine (List.pairwise_iff_forall_sublist.mpr ?_)
  intro a b hab x hx y hy
  have hmem₁ : a ∈ objectEntries db := hab.subset (by simp)
  have hmem₂ : b ∈ objectEntries db := hab.subset (by simp)
  have hlab : a.1 < b.1 :=
    (List.pairwise_iff_forall_sublist.mp hlt) hab
  obtain ⟨la, oa⟩ := a
  obtain ⟨lb, ob⟩ := b
  cases oa with
  | var va =>
      cases ob with
      | var vb =>
          have hxa : va = x := by simpa using hx
          have hyb : vb = y := by simpa using hy
          have hla : va = la := by
            simpa [objectEmbeddedNameMatches] using
              hguard (la, .var va) hmem₁
          have hlb : vb = lb := by
            simpa [objectEmbeddedNameMatches] using
              hguard (lb, .var vb) hmem₂
          rw [← hxa, ← hyb, hla, hlb]
          exact hlab
      | const cb => exact nomatch hy
      | hyp ess f e => exact nomatch hy
      | assert f fr e => exact nomatch hy
  | const ca => exact nomatch hx
  | hyp ess f e => exact nomatch hx
  | assert f fr e => exact nomatch hx

set_option maxHeartbeats 2000000 in
/-- **Constant-declaration lane discharge**: inserting the constant
object for a fresh name projects to the canonical after-view. -/
theorem projectSourcePrefix?_insertConst {db : RuntimeDB}
    {before after : SourceState} {name : String}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? name = none)
    (hafter : after = { before with
      declaredConstants := before.declaredConstants ++ [name] })
    (hvalid : sourceStateValid after = true) :
    projectSourcePrefix?
        (insertObj db name (.const name)) =
      some (runtimePrefix after).toProjection := by
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, hyps₀, hhyps, h7, asserts₀,
    hasserts, -, hrec⟩ := projectPrefix?_ok_inv hproj
  have hhypsB : hyps₀ = before.activeHypotheses := by
    have := congrArg PrefixProjection.activeHypotheses hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  subst hhypsB
  have hdcA : after.declaredConstants =
      before.declaredConstants ++ [name] := by rw [hafter]
  have hdvA : after.declaredVariables =
      before.declaredVariables := by rw [hafter]
  show projectPrefix?
    (insertObj (projectionDB db) name (.const name)) = _
  set dbC : RuntimeDB :=
    insertObj (projectionDB db) name (.const name) with hdbC
  have hfreshP : (projectionDB db).find? name = none := hfresh
  obtain ⟨pre, post, hsplitOld, hsplitNew, -⟩ :=
    objectEntries_insert_fresh
      (db := projectionDB db) (obj := .const name) hfreshP
  have hwff : (projectionDB db).wellFormedFrame?
      (projectionDB db).frame = true := by
    have hh := h2
    rw [DB.wellFormed?, Bool.and_eq_true] at hh
    exact hh.1
  have hwfo : (projectionDB db).wellFormedObjects? = true := by
    have hh := h2
    rw [DB.wellFormed?, Bool.and_eq_true] at hh
    exact hh.2
  have hres : ∀ lbl ∈ (projectionDB db).frame.hyps.toList,
      (projectionDB db).find? lbl ≠ none := by
    have hh := hwff
    rw [DB.wellFormedFrame?, Bool.and_eq_true] at hh
    exact resolve_of_frameHypsOk hh.1
  have h1' : dbC.error?.isNone = true := h1
  have h2' : dbC.wellFormed? = true :=
    wellFormed?_insertObj hfreshP h2 rfl
  have h3' : dbC.assertDvVarsInFrame? = true :=
    assertDvVarsInFrame?_insertObj hfreshP hwfo h3 trivial
  have h4' : rawCallerDVStrict dbC = true := by
    rw [rawCallerDVStrict_insertObj]
    exact h4
  have h5' : ((objectEntries dbC).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true := by
    rw [hsplitNew]
    refine embeddedNames_split ?_ (by simp [objectEmbeddedNameMatches])
    rw [← hsplitOld]
    exact h5
  have hdvNewList : declaredVariableNames (objectEntries dbC) =
      declaredVariableNames (objectEntries (projectionDB db)) := by
    rw [hsplitNew, hsplitOld, declaredVariableNames_append,
      declaredVariableNames_append, declaredVariableNames_cons_const]
  have h6' : ((declaredConstantNames (objectEntries dbC)).all
      fun c => !((declaredVariableNames
        (objectEntries dbC)).contains c)) = true := by
    rw [List.all_eq_true]
    intro c hc
    rw [hdvNewList]
    rw [hsplitNew, declaredConstantNames_append,
      declaredConstantNames_cons_const] at hc
    have hold : c ∈ declaredConstantNames (objectEntries
        (projectionDB db)) ∨ c = name := by
      rcases List.mem_append.mp hc with hpre | hrest
      · exact Or.inl (by
          rw [hsplitOld, declaredConstantNames_append]
          exact List.mem_append_left _ hpre)
      · rcases List.mem_cons.mp hrest with rfl | hpost
        · exact Or.inr rfl
        · exact Or.inl (by
            rw [hsplitOld, declaredConstantNames_append]
            exact List.mem_append_right _ hpost)
    rcases hold with hmem | rfl
    · rw [List.all_eq_true] at h6
      exact h6 c hmem
    · simp only [Bool.not_eq_true']
      rw [List.contains_eq_mem, decide_eq_false_iff_not]
      intro hmemv
      exact find?_of_mem_declaredVariableNames h5 hmemv hfreshP
  have hhyps' : projectHypotheses? dbC dbC.frame.hyps.toList =
      some before.activeHypotheses := by
    have hcong : projectHypotheses? dbC
        (projectionDB db).frame.hyps.toList =
        projectHypotheses? (projectionDB db)
          (projectionDB db).frame.hyps.toList :=
      projectHypotheses?_congr (fun lbl hl =>
        find?_insertObj_occupied hfreshP (hres lbl hl))
    show projectHypotheses? dbC
      (projectionDB db).frame.hyps.toList = _
    rw [hcong]
    exact hhyps
  have hcfEq : proofFacingCallerFrame dbC =
      proofFacingCallerFrame (projectionDB db) :=
    proofFacingCallerFrame_insertObj hfreshP hres
  have h7' : frameProjectionValid (proofFacingCallerFrame dbC)
      before.activeHypotheses = true := by
    rw [hcfEq]
    exact h7
  have hasserts' : projectAssertionsFromEntries? dbC
      (objectEntries dbC) = some asserts₀ := by
    have hassertsC : projectAssertionsFromEntries? dbC
        (objectEntries (projectionDB db)) = some asserts₀ :=
      projectAssertionsFromEntries?_congr hasserts
        (fun e he f fr emb heq lbl hlbl => by
          have hwfe := hwfo
          rw [DB.wellFormedObjects?, List.all_eq_true] at hwfe
          have hkv := hwfe e ((mem_objectEntries_iff _ e).mp he)
          rw [heq, DB.wellFormedObj?, Bool.and_eq_true] at hkv
          have hfr := hkv.2
          rw [DB.wellFormedFrame?, Bool.and_eq_true] at hfr
          exact find?_insertObj_occupied hfreshP
            (resolve_of_frameHypsOk hfr.1 lbl hlbl))
    rw [hsplitNew]
    rw [hsplitOld] at hassertsC
    obtain ⟨vpre, vpost, hvpre, hvpost, hviews⟩ :=
      projectAssertionsFromEntries?_split_inv hassertsC
    rw [hviews]
    refine projectAssertionsFromEntries?_append hvpre ?_
    rw [projectAssertionsFromEntries?_skip
      (by intro f fr emb hc; exact nomatch hc)]
    exact hvpost
  have hdcOld : declaredConstantNames (objectEntries
      (projectionDB db)) = sortStrings before.declaredConstants := by
    have h := congrArg PrefixProjection.declaredConstants hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using h.symm
  have hdvOld : declaredVariableNames (objectEntries
      (projectionDB db)) = sortStrings before.declaredVariables := by
    have h := congrArg PrefixProjection.declaredVariables hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using h.symm
  have hcfOld : proofFacingCallerFrame (projectionDB db) =
      before.callerFrame.toRuntime := by
    have h := congrArg PrefixProjection.callerFrame hrec
    simpa [SourcePrefix.toProjection, runtimePrefix,
      SourceFrame.toRuntime] using h.symm
  have hndAfter : after.declaredConstants.Nodup := by
    have hobj := objectNames_nodup_of_sourceStateValid
      (state := after) hvalid
    rw [SourceState.objectNames] at hobj
    exact (List.nodup_append.mp (List.nodup_append.mp hobj).1).1
  have hdcNew : declaredConstantNames (objectEntries dbC) =
      sortStrings after.declaredConstants := by
    rw [hdcA]
    have h₁' : (declaredConstantNames (objectEntries dbC)).Perm
        (name :: declaredConstantNames
          (objectEntries (projectionDB db))) := by
      rw [hsplitNew, hsplitOld, declaredConstantNames_append,
        declaredConstantNames_append, declaredConstantNames_cons_const]
      exact List.perm_middle
    have h₂ : (declaredConstantNames (objectEntries
        (projectionDB db))).Perm before.declaredConstants := by
      rw [hdcOld]
      exact List.mergeSort_perm _ _
    have h₃ : (before.declaredConstants ++ [name]).Perm
        (sortStrings (before.declaredConstants ++ [name])) :=
      (List.mergeSort_perm _ _).symm
    have hpermC : (declaredConstantNames (objectEntries dbC)).Perm
        (sortStrings (before.declaredConstants ++ [name])) :=
      h₁'.trans ((List.Perm.cons name h₂).trans
        (((List.perm_append_singleton name
          before.declaredConstants).symm).trans h₃))
    have hndA : (before.declaredConstants ++ [name]).Nodup := by
      rw [← hdcA]
      exact hndAfter
    exact eq_of_perm_of_pairwise_lt
      (fun a b hab hba => absurd (lt_trans hab hba) (lt_irrefl _))
      hpermC (declaredConstantNames_pairwise_lt h5')
      (sortStrings_pairwise_lt hndA)
  have hdvNew : declaredVariableNames (objectEntries dbC) =
      sortStrings after.declaredVariables := by
    rw [hdvNewList, hdvOld, hdvA]
  have hcfNew : proofFacingCallerFrame dbC =
      after.callerFrame.toRuntime := by
    rw [hcfEq, hcfOld, hafter]
    rfl
  have hrecEq : asserts₀ =
      (runtimePrefix after).toProjection.assertions := by
    have hthis : (runtimePrefix before).toProjection.assertions =
        asserts₀ := by
      simpa using congrArg PrefixProjection.assertions hrec
    rw [← hthis]
    have hassertsEq : after.assertions = before.assertions := by
      rw [hafter]
    simp [runtimePrefix, SourcePrefix.toProjection, hassertsEq]
  have hact : before.activeHypotheses = after.activeHypotheses := by
    rw [hafter]
  have hfinal := projectPrefix?_eq_some_of (db := dbC)
    h1' h2' h3' h4' h5' h6' hhyps' h7' hasserts' (by
      rw [hrecEq, hdcNew, hdvNew, hcfNew, hact]
      have hdcT : sortStrings after.declaredConstants =
          (runtimePrefix after).toProjection.declaredConstants := by
        simp [runtimePrefix, SourcePrefix.toProjection]
      have hdvT : sortStrings after.declaredVariables =
          (runtimePrefix after).toProjection.declaredVariables := by
        simp [runtimePrefix, SourcePrefix.toProjection]
      have hcfT : after.callerFrame.toRuntime =
          (runtimePrefix after).toProjection.callerFrame := by
        simp [runtimePrefix, SourcePrefix.toProjection,
          SourceFrame.toRuntime]
      have hahT : after.activeHypotheses =
          (runtimePrefix after).toProjection.activeHypotheses := by
        simp [runtimePrefix, SourcePrefix.toProjection]
      rw [hdcT, hdvT, hcfT, hahT]
      exact prefixProjectionValid_runtimePrefix hvalid)
  rw [hfinal]
  congr 1
  rw [hdcNew, hdvNew, hcfNew, hrecEq, hact]
  simp [runtimePrefix, SourcePrefix.toProjection,
    SourceFrame.toRuntime]

set_option maxHeartbeats 2000000 in
/-- **Variable-declaration lane discharge**: inserting the variable
object for a fresh name projects to the canonical after-view. -/
theorem projectSourcePrefix?_insertVar {db : RuntimeDB}
    {before after : SourceState} {name : String}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? name = none)
    (hafter : after = { before with
      declaredVariables := before.declaredVariables ++ [name] })
    (hvalid : sourceStateValid after = true) :
    projectSourcePrefix?
        (insertObj db name (.var name)) =
      some (runtimePrefix after).toProjection := by
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, hyps₀, hhyps, h7, asserts₀,
    hasserts, -, hrec⟩ := projectPrefix?_ok_inv hproj
  have hhypsB : hyps₀ = before.activeHypotheses := by
    have := congrArg PrefixProjection.activeHypotheses hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using this.symm
  subst hhypsB
  have hdcA : after.declaredConstants =
      before.declaredConstants := by rw [hafter]
  have hdvA : after.declaredVariables =
      before.declaredVariables ++ [name] := by rw [hafter]
  show projectPrefix?
    (insertObj (projectionDB db) name (.var name)) = _
  set dbV : RuntimeDB :=
    insertObj (projectionDB db) name (.var name) with hdbV
  have hfreshP : (projectionDB db).find? name = none := hfresh
  obtain ⟨pre, post, hsplitOld, hsplitNew, -⟩ :=
    objectEntries_insert_fresh
      (db := projectionDB db) (obj := .var name) hfreshP
  have hwff : (projectionDB db).wellFormedFrame?
      (projectionDB db).frame = true := by
    have hh := h2
    rw [DB.wellFormed?, Bool.and_eq_true] at hh
    exact hh.1
  have hwfo : (projectionDB db).wellFormedObjects? = true := by
    have hh := h2
    rw [DB.wellFormed?, Bool.and_eq_true] at hh
    exact hh.2
  have hres : ∀ lbl ∈ (projectionDB db).frame.hyps.toList,
      (projectionDB db).find? lbl ≠ none := by
    have hh := hwff
    rw [DB.wellFormedFrame?, Bool.and_eq_true] at hh
    exact resolve_of_frameHypsOk hh.1
  have h1' : dbV.error?.isNone = true := h1
  have h2' : dbV.wellFormed? = true :=
    wellFormed?_insertObj hfreshP h2 (by
      show (name == name) = true
      simp)
  have h3' : dbV.assertDvVarsInFrame? = true :=
    assertDvVarsInFrame?_insertObj hfreshP hwfo h3 trivial
  have h4' : rawCallerDVStrict dbV = true := by
    rw [rawCallerDVStrict_insertObj]
    exact h4
  have h5' : ((objectEntries dbV).all fun e =>
      objectEmbeddedNameMatches e.1 e.2) = true := by
    rw [hsplitNew]
    refine embeddedNames_split ?_ (by simp [objectEmbeddedNameMatches])
    rw [← hsplitOld]
    exact h5
  have hdcNewList : declaredConstantNames (objectEntries dbV) =
      declaredConstantNames (objectEntries (projectionDB db)) := by
    rw [hsplitNew, hsplitOld, declaredConstantNames_append,
      declaredConstantNames_append, declaredConstantNames_cons_var]
  have h6' : ((declaredConstantNames (objectEntries dbV)).all
      fun c => !((declaredVariableNames
        (objectEntries dbV)).contains c)) = true := by
    rw [List.all_eq_true]
    intro c hc
    rw [hdcNewList] at hc
    have hcocc : (projectionDB db).find? c ≠ none :=
      find?_of_mem_declaredConstantNames h5 hc
    simp only [Bool.not_eq_true']
    rw [List.contains_eq_mem, decide_eq_false_iff_not]
    intro hmemv
    rw [hsplitNew, declaredVariableNames_append,
      declaredVariableNames_cons_var] at hmemv
    rcases List.mem_append.mp hmemv with hpre | hrest
    · have hmemOld : c ∈ declaredVariableNames
          (objectEntries (projectionDB db)) := by
        rw [hsplitOld, declaredVariableNames_append]
        exact List.mem_append_left _ hpre
      rw [List.all_eq_true] at h6
      have := h6 c hc
      simp only [Bool.not_eq_true'] at this
      rw [List.contains_eq_mem, decide_eq_false_iff_not] at this
      exact this hmemOld
    · rcases List.mem_cons.mp hrest with rfl | hpost
      · exact hcocc hfreshP
      · have hmemOld : c ∈ declaredVariableNames
            (objectEntries (projectionDB db)) := by
          rw [hsplitOld, declaredVariableNames_append]
          exact List.mem_append_right _ hpost
        rw [List.all_eq_true] at h6
        have := h6 c hc
        simp only [Bool.not_eq_true'] at this
        rw [List.contains_eq_mem, decide_eq_false_iff_not] at this
        exact this hmemOld
  have hhyps' : projectHypotheses? dbV dbV.frame.hyps.toList =
      some before.activeHypotheses := by
    have hcong : projectHypotheses? dbV
        (projectionDB db).frame.hyps.toList =
        projectHypotheses? (projectionDB db)
          (projectionDB db).frame.hyps.toList :=
      projectHypotheses?_congr (fun lbl hl =>
        find?_insertObj_occupied hfreshP (hres lbl hl))
    show projectHypotheses? dbV
      (projectionDB db).frame.hyps.toList = _
    rw [hcong]
    exact hhyps
  have hcfEq : proofFacingCallerFrame dbV =
      proofFacingCallerFrame (projectionDB db) :=
    proofFacingCallerFrame_insertObj hfreshP hres
  have h7' : frameProjectionValid (proofFacingCallerFrame dbV)
      before.activeHypotheses = true := by
    rw [hcfEq]
    exact h7
  have hasserts' : projectAssertionsFromEntries? dbV
      (objectEntries dbV) = some asserts₀ := by
    have hassertsC : projectAssertionsFromEntries? dbV
        (objectEntries (projectionDB db)) = some asserts₀ :=
      projectAssertionsFromEntries?_congr hasserts
        (fun e he f fr emb heq lbl hlbl => by
          have hwfe := hwfo
          rw [DB.wellFormedObjects?, List.all_eq_true] at hwfe
          have hkv := hwfe e ((mem_objectEntries_iff _ e).mp he)
          rw [heq, DB.wellFormedObj?, Bool.and_eq_true] at hkv
          have hfr := hkv.2
          rw [DB.wellFormedFrame?, Bool.and_eq_true] at hfr
          exact find?_insertObj_occupied hfreshP
            (resolve_of_frameHypsOk hfr.1 lbl hlbl))
    rw [hsplitNew]
    rw [hsplitOld] at hassertsC
    obtain ⟨vpre, vpost, hvpre, hvpost, hviews⟩ :=
      projectAssertionsFromEntries?_split_inv hassertsC
    rw [hviews]
    refine projectAssertionsFromEntries?_append hvpre ?_
    rw [projectAssertionsFromEntries?_skip
      (by intro f fr emb hc; exact nomatch hc)]
    exact hvpost
  have hdcOld : declaredConstantNames (objectEntries
      (projectionDB db)) = sortStrings before.declaredConstants := by
    have h := congrArg PrefixProjection.declaredConstants hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using h.symm
  have hdvOld : declaredVariableNames (objectEntries
      (projectionDB db)) = sortStrings before.declaredVariables := by
    have h := congrArg PrefixProjection.declaredVariables hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using h.symm
  have hcfOld : proofFacingCallerFrame (projectionDB db) =
      before.callerFrame.toRuntime := by
    have h := congrArg PrefixProjection.callerFrame hrec
    simpa [SourcePrefix.toProjection, runtimePrefix,
      SourceFrame.toRuntime] using h.symm
  have hndAfter : after.declaredVariables.Nodup := by
    have hobj := objectNames_nodup_of_sourceStateValid
      (state := after) hvalid
    rw [SourceState.objectNames] at hobj
    exact (List.nodup_append.mp (List.nodup_append.mp hobj).1).2.1
  have hdvNew : declaredVariableNames (objectEntries dbV) =
      sortStrings after.declaredVariables := by
    rw [hdvA]
    have h₁' : (declaredVariableNames (objectEntries dbV)).Perm
        (name :: declaredVariableNames
          (objectEntries (projectionDB db))) := by
      rw [hsplitNew, hsplitOld, declaredVariableNames_append,
        declaredVariableNames_append, declaredVariableNames_cons_var]
      exact List.perm_middle
    have h₂ : (declaredVariableNames (objectEntries
        (projectionDB db))).Perm before.declaredVariables := by
      rw [hdvOld]
      exact List.mergeSort_perm _ _
    have h₃ : (before.declaredVariables ++ [name]).Perm
        (sortStrings (before.declaredVariables ++ [name])) :=
      (List.mergeSort_perm _ _).symm
    have hpermV : (declaredVariableNames (objectEntries dbV)).Perm
        (sortStrings (before.declaredVariables ++ [name])) :=
      h₁'.trans ((List.Perm.cons name h₂).trans
        (((List.perm_append_singleton name
          before.declaredVariables).symm).trans h₃))
    have hndA : (before.declaredVariables ++ [name]).Nodup := by
      rw [← hdvA]
      exact hndAfter
    exact eq_of_perm_of_pairwise_lt
      (fun a b hab hba => absurd (lt_trans hab hba) (lt_irrefl _))
      hpermV (declaredVariableNames_pairwise_lt h5')
      (sortStrings_pairwise_lt hndA)
  have hdcNew : declaredConstantNames (objectEntries dbV) =
      sortStrings after.declaredConstants := by
    rw [hdcNewList, hdcOld, hdcA]
  have hcfNew : proofFacingCallerFrame dbV =
      after.callerFrame.toRuntime := by
    rw [hcfEq, hcfOld, hafter]
    rfl
  have hrecEq : asserts₀ =
      (runtimePrefix after).toProjection.assertions := by
    have hthis : (runtimePrefix before).toProjection.assertions =
        asserts₀ := by
      simpa using congrArg PrefixProjection.assertions hrec
    rw [← hthis]
    have hassertsEq : after.assertions = before.assertions := by
      rw [hafter]
    simp [runtimePrefix, SourcePrefix.toProjection, hassertsEq]
  have hact : before.activeHypotheses = after.activeHypotheses := by
    rw [hafter]
  have hfinal := projectPrefix?_eq_some_of (db := dbV)
    h1' h2' h3' h4' h5' h6' hhyps' h7' hasserts' (by
      rw [hrecEq, hdcNew, hdvNew, hcfNew, hact]
      have hdcT : sortStrings after.declaredConstants =
          (runtimePrefix after).toProjection.declaredConstants := by
        simp [runtimePrefix, SourcePrefix.toProjection]
      have hdvT : sortStrings after.declaredVariables =
          (runtimePrefix after).toProjection.declaredVariables := by
        simp [runtimePrefix, SourcePrefix.toProjection]
      have hcfT : after.callerFrame.toRuntime =
          (runtimePrefix after).toProjection.callerFrame := by
        simp [runtimePrefix, SourcePrefix.toProjection,
          SourceFrame.toRuntime]
      have hahT : after.activeHypotheses =
          (runtimePrefix after).toProjection.activeHypotheses := by
        simp [runtimePrefix, SourcePrefix.toProjection]
      rw [hdcT, hdvT, hcfT, hahT]
      exact prefixProjectionValid_runtimePrefix hvalid)
  rw [hfinal]
  congr 1
  rw [hdcNew, hdvNew, hcfNew, hrecEq, hact]
  simp [runtimePrefix, SourcePrefix.toProjection,
    SourceFrame.toRuntime]

/-- Namespace agreement after any fresh insertion whose source step
adds exactly the label anywhere in the namespace. -/
theorem runtimeNamespaceAfterInsertMem {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {obj : Metamath.Verify.Object}
    (agreement : RuntimeDBAgrees db before)
    (hnames : ∀ candidate,
      candidate ∈ after.objectNames ↔
        candidate ∈ before.objectNames ∨ candidate = label) :
    RuntimeObjectNamespaceAgrees (insertObj db label obj) after := by
  refine ⟨?_, ?_⟩
  · show (insertObj db label obj).error? = none
    rw [insertObj_error]
    exact agreement.errorFree
  · intro candidate
    rw [hnames candidate, find?_insertObj]
    by_cases hsame : label = candidate
    · subst hsame
      simp
    · simp only [hsame, if_false]
      constructor
      · intro hocc
        exact Or.inl
          ((agreement.objectNamespace.occupied_iff candidate).mp hocc)
      · intro hmem
        rcases hmem with hold | hnew
        · exact (agreement.objectNamespace.occupied_iff
            candidate).mpr hold
        · exact absurd hnew.symm hsame

/-- **Constant-declaration co-evolution**: the shipped fresh insertion
of a constant object preserves complete agreement. -/
theorem RuntimeDBAgrees.insertConst' {db : RuntimeDB}
    {before after : SourceState} {name : String}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? name = none)
    (hafter : after = { before with
      declaredConstants := before.declaredConstants ++ [name] })
    (hvalid : sourceStateValid after = true) :
    RuntimeDBAgrees (insertObj db name (.const name)) after := by
  refine
    { projection :=
        projectSourcePrefix?_insertConst agreement hfresh hafter hvalid
      objectNamespace := ?_
      rawFrame := ⟨?_, ?_⟩
      scopeStack := ?_ }
  · refine runtimeNamespaceAfterInsertMem agreement ?_
    intro candidate
    rw [hafter]
    show candidate ∈ (before.declaredConstants ++ [name]) ++
      before.declaredVariables ++ before.usedLabels ↔ _
    rw [SourceState.objectNames]
    simp only [List.mem_append, List.mem_singleton]
    tauto
  · show db.frame.dj.toList = after.activeDistinctVariables
    rw [agreement.rawFrame.1, hafter]
  · show db.frame.hyps.toList =
      after.activeHypotheses.map HypothesisView.label
    rw [agreement.rawFrame.2, hafter]
  · show db.scopes.toList = runtimeScopeSizes after
    rw [agreement.scopeStack, hafter]
    rfl

/-- **Variable-declaration co-evolution**: the shipped fresh insertion
of a variable object preserves complete agreement. -/
theorem RuntimeDBAgrees.insertVar' {db : RuntimeDB}
    {before after : SourceState} {name : String}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? name = none)
    (hafter : after = { before with
      declaredVariables := before.declaredVariables ++ [name] })
    (hvalid : sourceStateValid after = true) :
    RuntimeDBAgrees (insertObj db name (.var name)) after := by
  refine
    { projection :=
        projectSourcePrefix?_insertVar agreement hfresh hafter hvalid
      objectNamespace := ?_
      rawFrame := ⟨?_, ?_⟩
      scopeStack := ?_ }
  · refine runtimeNamespaceAfterInsertMem agreement ?_
    intro candidate
    rw [hafter]
    show candidate ∈ before.declaredConstants ++
      (before.declaredVariables ++ [name]) ++ before.usedLabels ↔ _
    rw [SourceState.objectNames]
    simp only [List.mem_append, List.mem_singleton]
    tauto
  · show db.frame.dj.toList = after.activeDistinctVariables
    rw [agreement.rawFrame.1, hafter]
  · show db.frame.hyps.toList =
      after.activeHypotheses.map HypothesisView.label
    rw [agreement.rawFrame.2, hafter]
  · show db.scopes.toList = runtimeScopeSizes after
    rw [agreement.scopeStack, hafter]
    rfl

/-! ### The shipped per-symbol insertions

`DB.insert` is the real implementation operation for `$c`/`$v` tokens.
On the success path it reduces to `insertObj`; re-declaring an existing
variable as a variable is the shipped no-op branch. -/

/-- Symbol classification is authored into formulas, so declaration
membership checks are monotone in both declaration lists. -/
theorem formulaSymbolsRespectDeclarations_mono
    {dc dc' dv dv' : List String} {formula : ConstantHeadedFormula}
    (hdc : ∀ x ∈ dc, x ∈ dc') (hdv : ∀ x ∈ dv, x ∈ dv')
    (h : formulaSymbolsRespectDeclarations dc dv formula = true) :
    formulaSymbolsRespectDeclarations dc' dv' formula = true := by
  rw [formulaSymbolsRespectDeclarations, Bool.and_eq_true] at h ⊢
  refine ⟨?_, ?_⟩
  · have h1 := h.1
    rw [List.contains_eq_mem, decide_eq_true_iff] at h1 ⊢
    exact hdc _ h1
  · have h2 := h.2
    rw [List.all_eq_true] at h2 ⊢
    intro sym hsym
    have hs := h2 sym hsym
    cases sym with
    | const c =>
        have hs' : dc.contains c = true := hs
        show dc'.contains c = true
        rw [List.contains_eq_mem, decide_eq_true_iff] at hs' ⊢
        exact hdc _ hs'
    | var v =>
        have hs' : dv.contains v = true := hs
        show dv'.contains v = true
        rw [List.contains_eq_mem, decide_eq_true_iff] at hs' ⊢
        exact hdv _ hs'

/-- Assertion validity is monotone in the declaration lists. -/
theorem sourceAssertionValid_mono
    {dc dc' dv dv' : List String} {assertion : SourceAssertion}
    (hdc : ∀ x ∈ dc, x ∈ dc') (hdv : ∀ x ∈ dv, x ∈ dv')
    (h : sourceAssertionValid dc dv assertion = true) :
    sourceAssertionValid dc' dv' assertion = true := by
  rw [sourceAssertionValid] at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨⟨⟨h.1.1.1, h.1.1.2⟩, ?_⟩,
    formulaSymbolsRespectDeclarations_mono hdc hdv h.2⟩
  have hh := h.1.2
  rw [List.all_eq_true] at hh ⊢
  intro hyp hmem
  exact formulaSymbolsRespectDeclarations_mono hdc hdv (hh hyp hmem)

/-- Shipped constant insertion on the success path. -/
theorem insert_const_eq_insertObj {db : RuntimeDB}
    (herr : db.error? = none) (hscopes : db.scopes.size = 0)
    {name : String} (hfresh : db.find? name = none) (pos : Pos) :
    db.insert pos name (fun l => .const l) =
      insertObj db name (.const name) := by
  simp [DB.insert, DB.error, herr, hscopes, hfresh, insertObj]

/-- Shipped variable insertion on the fresh success path. -/
theorem insert_var_eq_insertObj {db : RuntimeDB}
    (herr : db.error? = none)
    {name : String} (hfresh : db.find? name = none) (pos : Pos) :
    db.insert pos name (fun l => .var l) =
      insertObj db name (.var name) := by
  simp [DB.insert, DB.error, herr, hfresh, insertObj]

/-- Shipped variable re-declaration is the accepted no-op branch. -/
theorem insert_var_eq_self_of_var {db : RuntimeDB}
    (herr : db.error? = none)
    {name existing : String}
    (hfound : db.find? name = some (.var existing)) (pos : Pos) :
    db.insert pos name (fun l => .var l) = db := by
  simp [DB.insert, DB.error, herr, hfound]

/-- Declared variables resolve to their own variable object. -/
theorem find?_var_of_mem_declaredVariables {db : RuntimeDB}
    {before : SourceState} {v : String}
    (agreement : RuntimeDBAgrees db before)
    (hv : v ∈ before.declaredVariables) :
    db.find? v = some (.var v) := by
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj
  obtain ⟨-, -, -, -, h5, -, hyps₀, -, -, asserts₀, -, -, hrec⟩ :=
    projectPrefix?_ok_inv hproj
  have hdvOld : declaredVariableNames (objectEntries
      (projectionDB db)) = sortStrings before.declaredVariables := by
    have h := congrArg PrefixProjection.declaredVariables hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using h.symm
  have hmem : v ∈ declaredVariableNames
      (objectEntries (projectionDB db)) := by
    rw [hdvOld, mem_sortStrings_iff]
    exact hv
  obtain ⟨entry, hentry, hextract⟩ := List.mem_filterMap.mp hmem
  obtain ⟨l, obj⟩ := entry
  cases obj with
  | var w =>
      have hw : w = v := by simpa using hextract
      subst hw
      rw [List.all_eq_true] at h5
      have hlabel : w = l := by
        simpa [objectEmbeddedNameMatches] using
          h5 (l, .var w) hentry
      subst hlabel
      exact find?_of_mem_objectEntries hentry
  | const c => exact nomatch hextract
  | hyp ess f e => exact nomatch hextract
  | assert f fr e => exact nomatch hextract

/-- Declared constants resolve to their own constant object. -/
theorem find?_const_of_mem_declaredConstants {db : RuntimeDB}
    {before : SourceState} {c : String}
    (agreement : RuntimeDBAgrees db before)
    (hc : c ∈ before.declaredConstants) :
    db.find? c = some (.const c) := by
  have hproj := agreement.projection
  unfold projectSourcePrefix? at hproj
  obtain ⟨-, -, -, -, h5, -, hyps₀, -, -, asserts₀, -, -, hrec⟩ :=
    projectPrefix?_ok_inv hproj
  have hdcOld : declaredConstantNames (objectEntries
      (projectionDB db)) = sortStrings before.declaredConstants := by
    have h := congrArg PrefixProjection.declaredConstants hrec
    simpa [SourcePrefix.toProjection, runtimePrefix] using h.symm
  have hmem : c ∈ declaredConstantNames
      (objectEntries (projectionDB db)) := by
    rw [hdcOld, mem_sortStrings_iff]
    exact hc
  obtain ⟨entry, hentry, hextract⟩ := List.mem_filterMap.mp hmem
  obtain ⟨l, obj⟩ := entry
  cases obj with
  | const w =>
      have hw : w = c := by simpa using hextract
      subst hw
      rw [List.all_eq_true] at h5
      have hlabel : w = l := by
        simpa [objectEmbeddedNameMatches] using
          h5 (l, .const w) hentry
      subst hlabel
      exact find?_of_mem_objectEntries hentry
  | var v => exact nomatch hextract
  | hyp ess f e => exact nomatch hextract
  | assert f fr e => exact nomatch hextract

/-! ### Intermediate validity between accepted endpoints

The multi-name `$c`/`$v` statements evolve the source state in one
step while the runtime inserts one symbol at a time.  Validity of the
intermediate pseudo-states sandwiches: uniqueness and disjointness
restrict from the accepted after-state, membership checks extend from
the accepted before-state. -/

@[simp] theorem toSourcePrefix_setDC (s : SourceState)
    (dc : List String) :
    ({ s with declaredConstants := dc } : SourceState).toSourcePrefix =
      { s.toSourcePrefix with declaredConstants := dc } := rfl

@[simp] theorem toSourcePrefix_setDV (s : SourceState)
    (dv : List String) :
    ({ s with declaredVariables := dv } : SourceState).toSourcePrefix =
      { s.toSourcePrefix with declaredVariables := dv } := rfl

@[simp] theorem objectNames_setDC (s : SourceState)
    (dc : List String) :
    ({ s with declaredConstants := dc } : SourceState).objectNames =
      dc ++ s.declaredVariables ++ s.usedLabels := rfl

@[simp] theorem objectNames_setDV (s : SourceState)
    (dv : List String) :
    ({ s with declaredVariables := dv } : SourceState).objectNames =
      s.declaredConstants ++ dv ++ s.usedLabels := rfl

theorem sourcePrefixValid_between_dc {p : SourcePrefix}
    {dcMid dcBig : List String}
    (hvb : sourcePrefixValid p = true)
    (hva : sourcePrefixValid
      ({ p with declaredConstants := dcBig } : SourcePrefix) = true)
    (hup : ∀ x ∈ p.declaredConstants, x ∈ dcMid)
    (hsubl : dcMid.Sublist dcBig) :
    sourcePrefixValid
      ({ p with declaredConstants := dcMid } : SourcePrefix) = true := by
  rw [sourcePrefixValid] at hvb hva ⊢
  simp only [Bool.and_eq_true] at hvb hva ⊢
  obtain ⟨⟨⟨⟨⟨⟨-, hdvB⟩, -⟩, hfrB⟩, hhypB⟩, hassB⟩, hlabB⟩ := hvb
  obtain ⟨⟨⟨⟨⟨⟨hdcA, -⟩, hdisA⟩, -⟩, -⟩, -⟩, -⟩ := hva
  refine ⟨⟨⟨⟨⟨⟨?_, hdvB⟩, ?_⟩, hfrB⟩, ?_⟩, ?_⟩, hlabB⟩
  · have hbig : dcBig.Nodup :=
      nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp hdcA)
    exact beq_iff_eq.mpr
      (eraseDups_length_eq_of_nodup _ (hbig.sublist hsubl))
  · rw [List.all_eq_true] at hdisA ⊢
    intro c hc
    exact hdisA c (hsubl.subset hc)
  · rw [List.all_eq_true] at hhypB ⊢
    intro hyp hmem
    have hb : formulaSymbolsRespectDeclarations
        p.declaredConstants p.declaredVariables hyp.formula = true :=
      hhypB hyp hmem
    exact formulaSymbolsRespectDeclarations_mono hup
      (fun x hx => hx) hb
  · rw [List.all_eq_true] at hassB ⊢
    intro assertion hmem
    exact sourceAssertionValid_mono hup (fun x hx => hx)
      (hassB assertion hmem)

theorem sourcePrefixValid_between_dv {p : SourcePrefix}
    {dvMid dvBig : List String}
    (hvb : sourcePrefixValid p = true)
    (hva : sourcePrefixValid
      ({ p with declaredVariables := dvBig } : SourcePrefix) = true)
    (hup : ∀ x ∈ p.declaredVariables, x ∈ dvMid)
    (hsubl : dvMid.Sublist dvBig) :
    sourcePrefixValid
      ({ p with declaredVariables := dvMid } : SourcePrefix) = true := by
  rw [sourcePrefixValid] at hvb hva ⊢
  simp only [Bool.and_eq_true] at hvb hva ⊢
  obtain ⟨⟨⟨⟨⟨⟨hdcB, -⟩, -⟩, hfrB⟩, hhypB⟩, hassB⟩, hlabB⟩ := hvb
  obtain ⟨⟨⟨⟨⟨⟨-, hdvA⟩, hdisA⟩, -⟩, -⟩, -⟩, -⟩ := hva
  refine ⟨⟨⟨⟨⟨⟨hdcB, ?_⟩, ?_⟩, hfrB⟩, ?_⟩, ?_⟩, hlabB⟩
  · have hbig : dvBig.Nodup :=
      nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp hdvA)
    exact beq_iff_eq.mpr
      (eraseDups_length_eq_of_nodup _ (hbig.sublist hsubl))
  · rw [List.all_eq_true] at hdisA ⊢
    intro c hc
    have := hdisA c hc
    simp only [Bool.not_eq_true'] at this ⊢
    rw [List.contains_eq_mem, decide_eq_false_iff_not] at this ⊢
    intro hmem
    exact this (hsubl.subset hmem)
  · rw [List.all_eq_true] at hhypB ⊢
    intro hyp hmem
    have hb : formulaSymbolsRespectDeclarations
        p.declaredConstants p.declaredVariables hyp.formula = true :=
      hhypB hyp hmem
    exact formulaSymbolsRespectDeclarations_mono
      (fun x hx => hx) hup hb
  · rw [List.all_eq_true] at hassB ⊢
    intro assertion hmem
    exact sourceAssertionValid_mono (fun x hx => hx) hup
      (hassB assertion hmem)

theorem sourceStateValid_between_dc {s : SourceState}
    {dcMid dcBig : List String}
    (hvb : sourceStateValid s = true)
    (hva : sourceStateValid
      ({ s with declaredConstants := dcBig } : SourceState) = true)
    (hup : ∀ x ∈ s.declaredConstants, x ∈ dcMid)
    (hsubl : dcMid.Sublist dcBig) :
    sourceStateValid
      ({ s with declaredConstants := dcMid } : SourceState) = true := by
  rw [sourceStateValid] at hvb hva ⊢
  simp only [Bool.and_eq_true] at hvb hva ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hpvB, hlabB⟩, hnodB⟩, hhcB⟩, hacB⟩, -⟩, hpairB⟩,
    hbndB⟩ := hvb
  obtain ⟨⟨⟨⟨⟨⟨⟨hpvA, -⟩, -⟩, -⟩, -⟩, honA⟩, -⟩, -⟩ := hva
  refine ⟨⟨⟨⟨⟨⟨⟨?_, hlabB⟩, hnodB⟩, hhcB⟩, hacB⟩, ?_⟩, hpairB⟩,
    hbndB⟩
  · rw [toSourcePrefix_setDC]
    refine sourcePrefixValid_between_dc hpvB ?_ hup hsubl
    rw [← toSourcePrefix_setDC]
    exact hpvA
  · rw [objectNames_setDC]
    rw [objectNames_setDC] at honA
    have hbig : (dcBig ++ s.declaredVariables ++
        s.usedLabels).Nodup :=
      nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp honA)
    have hsub : (dcMid ++ s.declaredVariables ++
        s.usedLabels).Sublist
        (dcBig ++ s.declaredVariables ++ s.usedLabels) :=
      (hsubl.append_right _).append_right _
    exact beq_iff_eq.mpr
      (eraseDups_length_eq_of_nodup _ (hbig.sublist hsub))

theorem sourceStateValid_between_dv {s : SourceState}
    {dvMid dvBig : List String}
    (hvb : sourceStateValid s = true)
    (hva : sourceStateValid
      ({ s with declaredVariables := dvBig } : SourceState) = true)
    (hup : ∀ x ∈ s.declaredVariables, x ∈ dvMid)
    (hsubl : dvMid.Sublist dvBig) :
    sourceStateValid
      ({ s with declaredVariables := dvMid } : SourceState) = true := by
  rw [sourceStateValid] at hvb hva ⊢
  simp only [Bool.and_eq_true] at hvb hva ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hpvB, hlabB⟩, hnodB⟩, hhcB⟩, hacB⟩, -⟩, hpairB⟩,
    hbndB⟩ := hvb
  obtain ⟨⟨⟨⟨⟨⟨⟨hpvA, -⟩, -⟩, -⟩, -⟩, honA⟩, -⟩, -⟩ := hva
  refine ⟨⟨⟨⟨⟨⟨⟨?_, hlabB⟩, hnodB⟩, hhcB⟩, hacB⟩, ?_⟩, ?_⟩,
    hbndB⟩
  · rw [toSourcePrefix_setDV]
    refine sourcePrefixValid_between_dv hpvB ?_ hup hsubl
    rw [← toSourcePrefix_setDV]
    exact hpvA
  · rw [objectNames_setDV]
    rw [objectNames_setDV] at honA
    have hbig : (s.declaredConstants ++ dvBig ++
        s.usedLabels).Nodup :=
      nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp honA)
    have hsub : (s.declaredConstants ++ dvMid ++
        s.usedLabels).Sublist
        (s.declaredConstants ++ dvBig ++ s.usedLabels) :=
      ((hsubl.append_left _).append_right _)
    exact beq_iff_eq.mpr
      (eraseDups_length_eq_of_nodup _ (hbig.sublist hsub))
  · rw [List.all_eq_true] at hpairB ⊢
    intro pair hmem
    have hb := hpairB pair hmem
    simp only [Bool.and_eq_true] at hb ⊢
    refine ⟨⟨hb.1.1, ?_⟩, ?_⟩
    · have := hb.1.2
      rw [List.contains_eq_mem, decide_eq_true_iff] at this ⊢
      exact hup _ this
    · have := hb.2
      rw [List.contains_eq_mem, decide_eq_true_iff] at this ⊢
      exact hup _ this

/-! ### The multi-name statement composites

A `$c`/`$v` statement declares all its names in one source step while
the shipped checker inserts one symbol per math token.  The runtime
fold of the real `DB.insert` co-evolves with the single source step. -/

/-- The deduplicating fold only ever appends. -/
theorem sublist_foldl_addVariableName :
    ∀ (names : List String) (dv : List String),
      dv.Sublist (names.foldl addVariableName dv)
  | [], _ => List.Sublist.refl _
  | n :: rest, dv => by
      rw [List.foldl_cons]
      refine List.Sublist.trans ?_
        (sublist_foldl_addVariableName rest (addVariableName dv n))
      unfold addVariableName
      split
      · exact List.Sublist.refl _
      · exact List.sublist_append_left _ _

private theorem foldConsts_agrees (pos : Pos) :
    ∀ {names : List String} {db : RuntimeDB} {before : SourceState},
      RuntimeDBAgrees db before →
      before.scopes = [] →
      sourceStateValid before = true →
      sourceStateValid ({ before with declaredConstants :=
        before.declaredConstants ++ names } : SourceState) = true →
      names.Nodup →
      (∀ n ∈ names, n ∉ before.objectNames) →
      RuntimeDBAgrees
        (names.foldl
          (fun d n => d.insert pos n (fun l => .const l)) db)
        ({ before with declaredConstants :=
          before.declaredConstants ++ names } : SourceState)
  | [], db, before, agreement, _, _, _, _, _ => by
      have heq : ({ before with declaredConstants :=
          before.declaredConstants ++ [] } : SourceState) = before := by
        simp
      rw [List.foldl_nil, heq]
      exact agreement
  | n :: rest, db, before, agreement, hscopes, hvb, hva, hnodup,
      hfreshAll => by
      have hmidValid : sourceStateValid
          ({ before with declaredConstants :=
            before.declaredConstants ++ [n] } : SourceState) = true :=
        sourceStateValid_between_dc hvb hva
          (fun x hx => List.mem_append_left _ hx)
          (List.Sublist.append_left
            ((List.nil_sublist rest).cons_cons n) _)
      have hmemN : n ∉ before.objectNames := hfreshAll n (by simp)
      have hfr : db.find? n = none := by
        cases hcase : db.find? n with
        | none => rfl
        | some obj =>
            exact absurd
              ((agreement.objectNamespace.occupied_iff n).mp
                (by simp [hcase])) hmemN
      have hstep : db.insert pos n (fun l => .const l) =
          insertObj db n (.const n) :=
        insert_const_eq_insertObj agreement.errorFree
          (by
            have hlen : db.scopes.toList.length = 0 := by
              rw [agreement.scopeStack]
              simp [runtimeScopeSizes, hscopes]
            simpa using hlen)
          hfr pos
      have hagreeMid : RuntimeDBAgrees (insertObj db n (.const n))
          ({ before with declaredConstants :=
            before.declaredConstants ++ [n] } : SourceState) :=
        RuntimeDBAgrees.insertConst' agreement hfr rfl hmidValid
      have hvaRec : sourceStateValid
          ({ ({ before with declaredConstants :=
              before.declaredConstants ++ [n] } : SourceState) with
            declaredConstants :=
              (before.declaredConstants ++ [n]) ++ rest }
            : SourceState) = true := by
        have hrw : (before.declaredConstants ++ [n]) ++ rest =
            before.declaredConstants ++ (n :: rest) := by
          simp
        rw [hrw]
        exact hva
      have hfreshRec : ∀ m ∈ rest,
          m ∉ ({ before with declaredConstants :=
            before.declaredConstants ++ [n] } : SourceState
              ).objectNames := by
        intro m hm
        have hmm : m ∉ before.objectNames :=
          hfreshAll m (List.mem_cons_of_mem _ hm)
        have hne : m ≠ n := by
          intro heq
          exact (List.nodup_cons.mp hnodup).1 (heq ▸ hm)
        rw [objectNames_setDC]
        rw [SourceState.objectNames] at hmm
        intro hmem
        rcases List.mem_append.mp hmem with hmem₁ | hlab
        · rcases List.mem_append.mp hmem₁ with hdc | hdv
          · rcases List.mem_append.mp hdc with hdcOld | hsing
            · exact hmm (List.mem_append_left _
                (List.mem_append_left _ hdcOld))
            · exact hne (List.mem_singleton.mp hsing)
          · exact hmm (List.mem_append_left _
              (List.mem_append_right _ hdv))
        · exact hmm (List.mem_append_right _ hlab)
      have hrec := foldConsts_agrees pos
        (names := rest) (db := insertObj db n (.const n))
        hagreeMid (by rw [show ({ before with declaredConstants :=
          before.declaredConstants ++ [n] } : SourceState).scopes =
            before.scopes from rfl]; exact hscopes)
        hmidValid hvaRec (List.nodup_cons.mp hnodup).2 hfreshRec
      rw [List.foldl_cons, hstep]
      have hafterEq : ({ ({ before with declaredConstants :=
          before.declaredConstants ++ [n] } : SourceState) with
            declaredConstants :=
              (before.declaredConstants ++ [n]) ++ rest }
            : SourceState) =
          ({ before with declaredConstants :=
            before.declaredConstants ++ (n :: rest) }
            : SourceState) := by
        simp
      rw [hafterEq] at hrec
      exact hrec

/-- **`$c` statement co-evolution**: the shipped per-token constant
insertions co-evolve with the single accepted multi-name source step. -/
theorem RuntimeDBAgrees.declareConstants' {db : RuntimeDB}
    {before after : SourceState} {names : List String}
    (agreement : RuntimeDBAgrees db before)
    (hdecl : declareConstants? before names = some after)
    (pos : Pos) :
    RuntimeDBAgrees
      (names.foldl
        (fun d n => d.insert pos n (fun l => .const l)) db)
      after := by
  obtain ⟨hvb, hva, hscopes, hshape⟩ := declareConstants?_inv hdecl
  subst hshape
  have hnodupNames : names.Nodup ∧
      ∀ n ∈ names, n ∉ before.objectNames := by
    have hon := objectNames_nodup_of_sourceStateValid _ hva
    rw [objectNames_setDC] at hon
    obtain ⟨h12, hlab, hdisj3⟩ := List.nodup_append.mp hon
    obtain ⟨h1, hdv, hdisj2⟩ := List.nodup_append.mp h12
    obtain ⟨hdc, hnames, hdisj1⟩ := List.nodup_append.mp h1
    refine ⟨hnames, ?_⟩
    intro n hn
    rw [SourceState.objectNames]
    intro hmem
    rcases List.mem_append.mp hmem with hmem₁ | hlabmem
    · rcases List.mem_append.mp hmem₁ with hdcmem | hdvmem
      · exact hdisj1 n hdcmem n hn rfl
      · exact hdisj2 n (List.mem_append_right _ hn) n hdvmem rfl
    · exact hdisj3 n (List.mem_append_left _
        (List.mem_append_right _ hn)) n hlabmem rfl
  exact foldConsts_agrees pos agreement hscopes hvb hva
    hnodupNames.1 hnodupNames.2

/-- Declared names always land in the deduplicating fold. -/
theorem mem_foldl_addVariableName :
    ∀ {names : List String} (dv : List String) {n : String},
      n ∈ names → n ∈ names.foldl addVariableName dv
  | v :: rest, dv, n, hn => by
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hn with rfl | hrest
      · refine (sublist_foldl_addVariableName rest _).subset ?_
        unfold addVariableName
        split
        · next hmem =>
            exact List.contains_iff_mem.mp hmem
        · exact List.mem_append_right _ (by simp)
      · exact mem_foldl_addVariableName _ hrest

private theorem foldVars_agrees (pos : Pos) :
    ∀ {names : List String} {db : RuntimeDB} {before : SourceState},
      RuntimeDBAgrees db before →
      sourceStateValid before = true →
      sourceStateValid ({ before with declaredVariables :=
        (names.foldl addVariableName before.declaredVariables) }
          : SourceState) = true →
      (∀ n ∈ names, n ∉ before.declaredConstants ∧
        n ∉ before.usedLabels) →
      RuntimeDBAgrees
        (names.foldl
          (fun d n => d.insert pos n (fun l => .var l)) db)
        ({ before with declaredVariables :=
          (names.foldl addVariableName before.declaredVariables) }
            : SourceState)
  | [], db, before, agreement, _, _, _ => by
      rw [List.foldl_nil]
      exact agreement
  | v :: rest, db, before, agreement, hvb, hva, hfreshAll => by
      simp only [List.foldl_cons] at hva ⊢
      by_cases hv : v ∈ before.declaredVariables
      · have haVN : addVariableName before.declaredVariables v =
            before.declaredVariables := by
          simp [addVariableName, hv]
        have hstep : db.insert pos v (fun l => .var l) = db :=
          insert_var_eq_self_of_var agreement.errorFree
            (find?_var_of_mem_declaredVariables agreement hv) pos
        rw [haVN] at hva ⊢
        rw [hstep]
        exact foldVars_agrees pos agreement hvb hva
          (fun n hn => hfreshAll n (List.mem_cons_of_mem _ hn))
      · have haVN : addVariableName before.declaredVariables v =
            before.declaredVariables ++ [v] := by
          simp [addVariableName, hv]
        rw [haVN] at hva ⊢
        have hfr : db.find? v = none := by
          have hmemN : v ∉ before.objectNames := by
            rw [SourceState.objectNames]
            intro hmem
            rcases List.mem_append.mp hmem with hmem₁ | hlab
            · rcases List.mem_append.mp hmem₁ with hdc | hdv
              · exact (hfreshAll v (by simp)).1 hdc
              · exact hv hdv
            · exact (hfreshAll v (by simp)).2 hlab
          cases hcase : db.find? v with
          | none => rfl
          | some obj =>
              exact absurd
                ((agreement.objectNamespace.occupied_iff v).mp
                  (by simp [hcase])) hmemN
        have hmidValid : sourceStateValid
            ({ before with declaredVariables :=
              before.declaredVariables ++ [v] } : SourceState) =
              true :=
          sourceStateValid_between_dv hvb hva
            (fun x hx => List.mem_append_left _ hx)
            (sublist_foldl_addVariableName rest _)
        have hstep : db.insert pos v (fun l => .var l) =
            insertObj db v (.var v) :=
          insert_var_eq_insertObj agreement.errorFree hfr pos
        have hagreeMid : RuntimeDBAgrees (insertObj db v (.var v))
            ({ before with declaredVariables :=
              before.declaredVariables ++ [v] } : SourceState) :=
          RuntimeDBAgrees.insertVar' agreement hfr rfl hmidValid
        have hrec := foldVars_agrees pos (names := rest)
          hagreeMid hmidValid hva
          (fun n hn => hfreshAll n (List.mem_cons_of_mem _ hn))
        rw [hstep]
        exact hrec

/-- **`$v` statement co-evolution**: the shipped per-token variable
insertions (including accepted re-declaration no-ops) co-evolve with
the single accepted multi-name source step. -/
theorem RuntimeDBAgrees.declareVariables' {db : RuntimeDB}
    {before after : SourceState} {names : List String}
    (agreement : RuntimeDBAgrees db before)
    (hdecl : declareVariables? before names = some after)
    (pos : Pos) :
    RuntimeDBAgrees
      (names.foldl
        (fun d n => d.insert pos n (fun l => .var l)) db)
      after := by
  obtain ⟨hvb, hva, hshape⟩ := declareVariables?_inv hdecl
  subst hshape
  refine foldVars_agrees pos agreement hvb hva ?_
  intro n hn
  have hnFold : n ∈ names.foldl addVariableName
      before.declaredVariables :=
    mem_foldl_addVariableName _ hn
  have hon := objectNames_nodup_of_sourceStateValid _ hva
  rw [objectNames_setDV] at hon
  obtain ⟨h12, hlab, hdisj3⟩ := List.nodup_append.mp hon
  obtain ⟨hdc, hdv, hdisj2⟩ := List.nodup_append.mp h12
  refine ⟨?_, ?_⟩
  · intro hmem
    exact hdisj2 n hmem n hnFold rfl
  · intro hmem
    exact hdisj3 n (List.mem_append_right _ hnFold) n hmem rfl

end SymLane

/-! ## The shipped `$f`/`$e` statement operation

`DB.insertHyp` is the real implementation operation: shape checks, the
namespace insertion, and the frame push.  Under agreement with an
accepted source declaration every check passes, so the shipped
operation reduces to the composite already discharged by
`RuntimeDBAgrees.insertHyp'`. -/

section HypShippedLane

open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4

/-- The raw frame as the label image of the active hypotheses. -/
theorem frame_hyps_eq_label_array {db : RuntimeDB}
    {before : SourceState}
    (agreement : RuntimeDBAgrees db before) :
    db.frame.hyps =
      (before.activeHypotheses.map HypothesisView.label).toArray := by
  apply Array.ext'
  rw [agreement.rawFrame.2, List.toList_toArray]

/-- The shipped float-occurrence scan agrees with the projected
floating-variable names. -/
theorem floatVarOccursInFrame_iff {db : RuntimeDB}
    {before : SourceState}
    (agreement : RuntimeDBAgrees db before) (v : String) :
    db.floatVarOccursInFrame v = true ↔
      v ∈ floatingVariableNames before.activeHypotheses := by
  have hpoint : ∀ hyp ∈ before.activeHypotheses,
      projectHypothesis? db hyp.label = some hyp :=
    fun hyp hh => activeHyp_project_self agreement hyp hh
  constructor
  · intro h
    rw [DB.floatVarOccursInFrame, List.any_eq_true] at h
    obtain ⟨lbl, hlbl, hpred⟩ := h
    rw [agreement.rawFrame.2] at hlbl
    obtain ⟨hyp, hhyp, rfl⟩ := List.mem_map.mp hlbl
    obtain ⟨rf, hfind, hform, -⟩ :=
      projectHypothesis?_eq_some_fidelity db hyp.label hyp
        (hpoint hyp hhyp)
    rw [hfind] at hpred
    cases hyp with
    | essential lbl f =>
        simp [hypothesisEssentialBit] at hpred
    | floating lbl tc w =>
        have hrf : rf = (⟨tc, [.var w]⟩ :
            ConstantHeadedFormula).toRuntime :=
          (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
            simpa [HypothesisView.formula] using hform)
        subst hrf
        have hw : w = v := by
          simpa [hypothesisEssentialBit,
            ConstantHeadedFormula.toRuntime] using hpred
        subst hw
        exact List.mem_filterMap.mpr
          ⟨.floating lbl tc w, hhyp, by
            simp [HypothesisView.floatingVariable?]⟩
  · intro h
    obtain ⟨hyp, hhyp, hfv⟩ := List.mem_filterMap.mp h
    cases hyp with
    | essential lbl f =>
        exact nomatch hfv
    | floating lbl tc w =>
        have hw : w = v := by
          simpa [HypothesisView.floatingVariable?] using hfv
        subst hw
        obtain ⟨rf, hfind, hform, -⟩ :=
          projectHypothesis?_eq_some_fidelity db
            (HypothesisView.floating lbl tc w).label
            (.floating lbl tc w) (hpoint _ hhyp)
        have hrf : rf = (⟨tc, [.var w]⟩ :
            ConstantHeadedFormula).toRuntime :=
          (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
            simpa [HypothesisView.formula] using hform)
        subst hrf
        rw [DB.floatVarOccursInFrame, List.any_eq_true]
        refine ⟨lbl, ?_, ?_⟩
        · rw [agreement.rawFrame.2]
          exact List.mem_map.mpr ⟨.floating lbl tc w, hhyp, rfl⟩
        · rw [show (HypothesisView.floating lbl tc w).label = lbl
            from rfl] at hfind
          rw [hfind]
          simp [hypothesisEssentialBit,
            ConstantHeadedFormula.toRuntime]

/-- Every shipped hypothesis-shape check passes for an accepted source
declaration. -/
theorem insertHypChecks_eq_self {db : RuntimeDB}
    {before after : SourceState} {view : HypothesisView}
    (agreement : RuntimeDBAgrees db before)
    (hafter : after =
      { before with
        usedLabels := before.usedLabels ++ [view.label]
        activeHypotheses := before.activeHypotheses ++ [view] })
    (hvalid : sourceStateValid after = true) (pos : Pos) :
    db.insertHypChecks pos (hypothesisEssentialBit view)
      view.formula.toRuntime = db := by
  have hfv := sourcePrefixValid_of_sourceStateValid after hvalid
  simp only [sourcePrefixValid, Bool.and_eq_true,
    SourceState.toSourcePrefix] at hfv
  have hframe := hfv.1.1.1.2
  rw [sourceFrameValid] at hframe
  simp only [Bool.and_eq_true] at hframe
  have hfloats : db.frameFloatVars
      (⟨#[], db.frame.hyps⟩ : RuntimeFrame) =
      floatingVariableNames before.activeHypotheses := by
    rw [frame_hyps_eq_label_array agreement]
    exact frameFloatVars_of_pointwise
      (fun hyp hh => activeHyp_project_self agreement hyp hh)
  cases view with
  | essential lbl f =>
      have hrespect : formulaSymbolsRespectFrame
          (floatingVariableNames before.activeHypotheses) f = true := by
        have hall := hframe.1.2
        rw [List.all_eq_true] at hall
        have hmem : HypothesisView.essential lbl f ∈
            after.activeHypotheses := by
          rw [hafter]
          show HypothesisView.essential lbl f ∈
            before.activeHypotheses ++ [.essential lbl f]
          exact List.mem_append_right _ (by simp)
        have hthis := hall (.essential lbl f) hmem
        have hfl : floatingVariableNames after.activeHypotheses =
            floatingVariableNames before.activeHypotheses := by
          rw [hafter]
          show floatingVariableNames (before.activeHypotheses ++
            [.essential lbl f]) = _
          rw [floatingVariableNames, List.filterMap_append]
          simp [floatingVariableNames,
            HypothesisView.floatingVariable?]
        rw [hfl] at hthis
        exact hthis
      have hbridge : DB.formulaSymsRespectFrame db
          f.toRuntime
          (⟨#[], db.frame.hyps⟩ : RuntimeFrame) = true := by
        rw [formulaSymsRespectFrame_bridge hfloats]
        exact hrespect
      show db.insertHypChecks pos true f.toRuntime = db
      rw [DB.insertHypChecks]
      simp [DB.error, agreement.errorFree, hbridge]
  | floating lbl tc w =>
      have hnotin : w ∉ floatingVariableNames
          before.activeHypotheses := by
        have huniq := hframe.1.1.1.1.2
        rw [hafter] at huniq
        have huniq' : hasUniqueFloatingVariables
            (before.activeHypotheses ++
              [HypothesisView.floating lbl tc w]) = true := by
          simpa using huniq
        intro hmem
        rw [hasUniqueFloatingVariables] at huniq'
        have hnodup : (floatingVariableNames
            (before.activeHypotheses ++
              [HypothesisView.floating lbl tc w])).Nodup :=
          nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp huniq')
        rw [floatingVariableNames, List.filterMap_append] at hnodup
        have hw : (List.filterMap HypothesisView.floatingVariable?
            [HypothesisView.floating lbl tc w]) = [w] := by
          simp [HypothesisView.floatingVariable?]
        rw [hw] at hnodup
        obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnodup
        exact hdisj w hmem w (by simp) rfl
      have hocc : db.floatVarOccursInFrame w = false := by
        rw [← Bool.not_eq_true]
        intro hcontra
        exact hnotin ((floatVarOccursInFrame_iff agreement w).mp
          hcontra)
      rw [DB.insertHypChecks]
      simp [DB.error, agreement.errorFree, hypothesisEssentialBit,
        HypothesisView.formula, ConstantHeadedFormula.toRuntime,
        Formula.hasConstHead, Formula.isFloatShape, Sym.value, hocc]

/-- The shipped `$f`/`$e` operation reduces to the discharged
composite on the accepted path. -/
theorem insertHyp_eq_composite {db : RuntimeDB}
    {before after : SourceState} {view : HypothesisView}
    (agreement : RuntimeDBAgrees db before)
    (hfresh : db.find? view.label = none)
    (hafter : after =
      { before with
        usedLabels := before.usedLabels ++ [view.label]
        activeHypotheses := before.activeHypotheses ++ [view] })
    (hvalid : sourceStateValid after = true) (pos : Pos) :
    db.insertHyp pos view.label (hypothesisEssentialBit view)
        view.formula.toRuntime =
      ({ insertObj db view.label
          (.hyp (hypothesisEssentialBit view)
            view.formula.toRuntime view.label) with
        frame := ⟨db.frame.dj,
          db.frame.hyps.push view.label⟩ } : RuntimeDB) := by
  rw [DB.insertHyp,
    insertHypChecks_eq_self agreement hafter hvalid pos]
  simp [DB.insert, DB.error, agreement.errorFree, hfresh,
    DB.withHyps, DB.withFrame, insertObj]

/-- Freshness of a label appended by an accepted declaration. -/
theorem fresh_of_label_append {db : RuntimeDB}
    {before : SourceState} {label : String} {view : HypothesisView}
    (agreement : RuntimeDBAgrees db before)
    (hva : sourceStateValid
      ({ before with
        usedLabels := before.usedLabels ++ [label]
        activeHypotheses := before.activeHypotheses ++ [view] }
          : SourceState) = true) :
    db.find? label = none := by
  have hmemN : label ∉ before.objectNames := by
    have hon := objectNames_nodup_of_sourceStateValid _ hva
    rw [show ({ before with
        usedLabels := before.usedLabels ++ [label]
        activeHypotheses := before.activeHypotheses ++ [view] }
          : SourceState).objectNames =
        before.declaredConstants ++ before.declaredVariables ++
          (before.usedLabels ++ [label]) from rfl] at hon
    obtain ⟨h12, hlabnew, hdisj3⟩ := List.nodup_append.mp hon
    obtain ⟨-, -, hdisjLab⟩ := List.nodup_append.mp hlabnew
    rw [SourceState.objectNames]
    intro hmem
    rcases List.mem_append.mp hmem with hmem₁ | hlab
    · exact hdisj3 label hmem₁ label (List.mem_append_right _
        (by simp)) rfl
    · exact hdisjLab label hlab label (by simp) rfl
  cases hcase : db.find? label with
  | none => rfl
  | some obj =>
      exact absurd
        ((agreement.objectNamespace.occupied_iff label).mp
          (by simp [hcase])) hmemN

/-- **`$f` statement co-evolution against the shipped operation.** -/
theorem RuntimeDBAgrees.declareFloating' {db : RuntimeDB}
    {before after : SourceState}
    {label typecode variableName : String}
    (agreement : RuntimeDBAgrees db before)
    (hdecl : declareFloating? before label typecode variableName =
      some after) (pos : Pos) :
    RuntimeDBAgrees
      (db.insertHyp pos label
        (hypothesisEssentialBit
          (.floating label typecode variableName))
        (HypothesisView.floating label typecode
          variableName).formula.toRuntime)
      after := by
  obtain ⟨hvb, hva, hshape⟩ := declareFloating?_inv hdecl
  subst hshape
  have hfresh : db.find? label = none :=
    fresh_of_label_append
      (view := .floating label typecode variableName)
      agreement hva
  have hcomp := insertHyp_eq_composite agreement
    (view := .floating label typecode variableName)
    hfresh rfl hva pos
  rw [show (HypothesisView.floating label typecode
    variableName).label = label from rfl] at hcomp
  rw [hcomp]
  exact RuntimeDBAgrees.insertHyp'
    (view := .floating label typecode variableName)
    agreement hfresh rfl hva

/-- **`$e` statement co-evolution against the shipped operation.** -/
theorem RuntimeDBAgrees.declareEssential' {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (hdecl : declareEssential? before label formula = some after)
    (pos : Pos) :
    RuntimeDBAgrees
      (db.insertHyp pos label
        (hypothesisEssentialBit (.essential label formula))
        (HypothesisView.essential label
          formula).formula.toRuntime)
      after := by
  obtain ⟨hvb, hva, hshape⟩ := declareEssential?_inv hdecl
  subst hshape
  have hfresh : db.find? label = none :=
    fresh_of_label_append
      (view := .essential label formula)
      agreement hva
  have hcomp := insertHyp_eq_composite agreement
    (view := .essential label formula)
    hfresh rfl hva pos
  rw [show (HypothesisView.essential label formula).label = label
    from rfl] at hcomp
  rw [hcomp]
  exact RuntimeDBAgrees.insertHyp'
    (view := .essential label formula)
    agreement hfresh rfl hva

end HypShippedLane

/-! ## The shipped `$d` statement operation

The parser's `djvars` loop pushes one canonical pair per (prior, new)
token pair, in arrival order.  The accumulated database effect of an
accepted `$d` statement is therefore the pair-list fold below, which
collapses to the frame append already discharged by
`RuntimeDBAgrees.declareDisjoint'`. -/

section DjShippedLane

/-- Pushing a list of pairs one at a time appends the list. -/
theorem foldl_withDJ_push (db : RuntimeDB) :
    ∀ (pairs : List Metamath.Verify.DJ),
      pairs.foldl
        (fun d p => d.withDJ (fun dj => dj.push p)) db =
      ({ db with frame := ⟨db.frame.dj ++ pairs.toArray,
        db.frame.hyps⟩ } : RuntimeDB) := by
  suffices h : ∀ (pairs : List Metamath.Verify.DJ)
      (d : RuntimeDB),
      pairs.foldl (fun d p => d.withDJ (fun dj => dj.push p)) d =
        ({ d with frame := ⟨d.frame.dj ++ pairs.toArray,
          d.frame.hyps⟩ } : RuntimeDB) by
    intro pairs
    exact h pairs db
  intro pairs
  induction pairs with
  | nil =>
      intro d
      rw [List.foldl_nil]
      have hfr : (⟨d.frame.dj ++ ([] : List Metamath.Verify.DJ
          ).toArray, d.frame.hyps⟩ : RuntimeFrame) = d.frame := by
        apply congrArg₂ Metamath.Verify.Frame.mk
        · apply Array.ext'
          simp
        · rfl
      rw [hfr]
  | cons p rest ih =>
      intro d
      rw [List.foldl_cons, ih]
      show ({ d.withDJ (fun dj => dj.push p) with
        frame := ⟨(d.withDJ (fun dj => dj.push p)).frame.dj ++
          rest.toArray,
          (d.withDJ (fun dj => dj.push p)).frame.hyps⟩ }
            : RuntimeDB) = _
      have hdj : (d.withDJ (fun dj => dj.push p)).frame.dj =
          d.frame.dj.push p := by
        show (Metamath.Verify.DB.withDJ _ d).frame.dj = _
        unfold Metamath.Verify.DB.withDJ Metamath.Verify.DB.withFrame
        rcases hfr : d.frame with ⟨dj, hyps⟩
        rfl
      have hhyps : (d.withDJ (fun dj => dj.push p)).frame.hyps =
          d.frame.hyps := by
        show (Metamath.Verify.DB.withDJ _ d).frame.hyps = _
        unfold Metamath.Verify.DB.withDJ Metamath.Verify.DB.withFrame
        rcases hfr : d.frame with ⟨dj, hyps⟩
        rfl
      have hbase : ∀ (fr : RuntimeFrame),
          ({ d.withDJ (fun dj => dj.push p) with frame := fr }
            : RuntimeDB) = { d with frame := fr } := by
        intro fr
        show ({ Metamath.Verify.DB.withDJ _ d with frame := fr }
          : RuntimeDB) = _
        unfold Metamath.Verify.DB.withDJ Metamath.Verify.DB.withFrame
        rfl
      rw [hdj, hhyps, hbase]
      have harr : d.frame.dj.push p ++ rest.toArray =
          d.frame.dj ++ (p :: rest).toArray := by
        apply Array.ext'
        simp
      rw [harr]

/-- **`$d` statement co-evolution against the shipped pair pushes**:
the parser's per-pair `withDJ` pushes in arrival order co-evolve with
the single accepted multi-name source step. -/
theorem RuntimeDBAgrees.declareDisjoint'' {db : RuntimeDB}
    {before after : SourceState} {names : List String}
    (agreement : RuntimeDBAgrees db before)
    (hdecl : declareDisjoint? before names = some after) :
    RuntimeDBAgrees
      ((allDistinctDJ names).foldl
        (fun d p => d.withDJ (fun dj => dj.push p)) db)
      after := by
  rw [foldl_withDJ_push]
  exact RuntimeDBAgrees.declareDisjoint' agreement hdecl

end DjShippedLane

/-! ## The shipped mandatory-frame trim

`DB.trimFrame` computes the mandatory frame of a new assertion with
mutable loops.  The functional spelling below is proved equal by
re-uttering the loop body and converting each loop to a list fold; the
semantic bridge to the source `mandatoryFrame` builds on it. -/

section TrimLane

open Std (HashSet)
open Metamath.Verify
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4

def trimVarsOf (db : DB) (fmla : Formula) (fr : Frame) :
    HashSet String :=
  fr.hyps.toList.foldl
    (fun vars l =>
      match db.find? l with
      | some (.hyp true f _) => f.foldlVars vars HashSet.insert
      | _ => vars)
    (fmla.foldlVars ∅ HashSet.insert)

def trimDJOf (vars : HashSet String) (dj : Array DJ) : Array DJ :=
  dj.toList.foldl
    (fun acc v =>
      if (vars.contains v.1 && vars.contains v.2) = true then
        acc.push v
      else acc)
    #[]

def trimVarsWithFOf (db : DB) (vars : HashSet String)
    (fr : Frame) : HashSet String :=
  fr.hyps.toList.foldl
    (fun acc l =>
      match db.find? l with
      | some (.hyp false f _) =>
          if vars.contains (f[1]!.value) = true then
            acc.insert (f[1]!.value)
          else acc
      | _ => acc)
    ∅

def trimOkOf (vars varsWithF : HashSet String) : Bool :=
  vars.toList.foldl
    (fun ok v => if varsWithF.contains v = true then ok else false)
    true

private theorem forIn_list_yield_eq_foldl {α β : Type _}
    (g : β → α → β) :
    ∀ (ls : List α) (init : β),
      (forIn (m := Id) ls init
        (fun a b => pure (.yield (g b a)))) =
      ls.foldl g init
  | [], _ => rfl
  | a :: rest, init => by
      rw [List.forIn_cons]
      show (forIn (m := Id) rest (g init a)
        (fun a b => pure (.yield (g b a)))) = _
      rw [forIn_list_yield_eq_foldl g rest (g init a),
        List.foldl_cons]

set_option maxHeartbeats 1000000 in
theorem trimFrame_eq_functional (db : DB) (fmla : Formula)
    (fr : Frame) :
    db.trimFrame fmla fr =
      (trimOkOf (trimVarsOf db fmla fr)
          (trimVarsWithFOf db (trimVarsOf db fmla fr) fr),
        ⟨trimDJOf (trimVarsOf db fmla fr) fr.dj,
          DB.trimFrameHyps db (trimVarsOf db fmla fr) fr.hyps⟩) := by
  have hbody₁ : (fun (l : String) (r : HashSet String) =>
      match db.find? l with
      | some (.hyp true f _) =>
          pure (f := Id) (ForInStep.yield (f.foldlVars r HashSet.insert))
      | _ => pure (ForInStep.yield r)) =
      (fun l r => pure (ForInStep.yield
        (match db.find? l with
        | some (.hyp true f _) => f.foldlVars r HashSet.insert
        | _ => r))) := by
    funext l r
    rcases db.find? l with _ | obj
    · rfl
    · rcases obj with _ | _ | ⟨ess, f, e⟩ | _
      · rfl
      · rfl
      · rcases ess with _ | _ <;> rfl
      · rfl
  have hbody₂ : (fun (v : DJ) (dj : Array DJ) =>
      if ((trimVarsOf db fmla fr).contains v.1 &&
          (trimVarsOf db fmla fr).contains v.2) = true then
        pure (f := Id) (ForInStep.yield (dj.push v))
      else pure (ForInStep.yield dj)) =
      (fun v dj => pure (ForInStep.yield
        (if ((trimVarsOf db fmla fr).contains v.1 &&
            (trimVarsOf db fmla fr).contains v.2) = true then
          dj.push v
        else dj))) := by
    funext v dj
    by_cases h : ((trimVarsOf db fmla fr).contains v.1 &&
        (trimVarsOf db fmla fr).contains v.2) = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  have hbody₃ : (fun (l : String) (w : HashSet String) =>
      match db.find? l with
      | some (.hyp false f _) =>
          if (trimVarsOf db fmla fr).contains (f[1]!.value) = true then
            pure (f := Id) (ForInStep.yield (w.insert (f[1]!.value)))
          else pure (ForInStep.yield w)
      | _ => pure (ForInStep.yield w)) =
      (fun l w => pure (ForInStep.yield
        (match db.find? l with
        | some (.hyp false f _) =>
            if (trimVarsOf db fmla fr).contains (f[1]!.value) = true
            then w.insert (f[1]!.value)
            else w
        | _ => w))) := by
    funext l w
    rcases db.find? l with _ | obj
    · rfl
    · rcases obj with _ | _ | ⟨ess, f, e⟩ | _
      · rfl
      · rfl
      · rcases ess with _ | _
        · by_cases h : (trimVarsOf db fmla fr).contains
              (f[1]!.value) = true
          · simp only [if_pos h]
          · simp only [if_neg h]
        · rfl
      · rfl
  have hbody₄ : ∀ (varsWithF : HashSet String),
      (fun (v : String) (ok : Bool) =>
        if varsWithF.contains v = true then
          pure (f := Id) (ForInStep.yield ok)
        else pure (ForInStep.yield false)) =
      (fun v ok => pure (ForInStep.yield
        (if varsWithF.contains v = true then ok else false))) := by
    intro varsWithF
    funext v ok
    by_cases h : varsWithF.contains v = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  have key : db.trimFrame fmla fr = Id.run (do
      let collectVars (fmla : Formula) vars :=
        fmla.foldlVars vars HashSet.insert
      let mut vars : HashSet String := collectVars fmla ∅
      for l in fr.hyps do
        if let some (.hyp true f _) := db.find? l then
          vars := collectVars f vars
      let mut dj := #[]
      for v in fr.dj do
        if vars.contains v.1 && vars.contains v.2 then
          dj := dj.push v
      let hyps := DB.trimFrameHyps db vars fr.hyps
      let mut ok := true
      let mut varsWithF : HashSet String := ∅
      for l in fr.hyps do
        if let some (.hyp false f _) := db.find? l then
          let v := f[1]!.value
          if vars.contains v then
            varsWithF := varsWithF.insert v
      for v in vars do
        unless varsWithF.contains v do ok := false
      pure (ok, ⟨dj, hyps⟩)) := rfl
  rw [key]
  show (Bind.bind (m := Id)
      (forIn fr.hyps (fmla.foldlVars ∅ HashSet.insert)
        (fun l r =>
          match db.find? l with
          | some (.hyp true f _) =>
              pure (ForInStep.yield (f.foldlVars r HashSet.insert))
          | _ => pure (ForInStep.yield r)))
      (fun vars => Bind.bind (m := Id)
        (forIn fr.dj (#[] : Array DJ)
          (fun v dj =>
            if (vars.contains v.1 && vars.contains v.2) = true then
              pure (ForInStep.yield (dj.push v))
            else pure (ForInStep.yield dj)))
        (fun dj => Bind.bind (m := Id)
          (forIn fr.hyps (∅ : HashSet String)
            (fun l w =>
              match db.find? l with
              | some (.hyp false f _) =>
                  if vars.contains (f[1]!.value) = true then
                    pure (ForInStep.yield (w.insert (f[1]!.value)))
                  else pure (ForInStep.yield w)
              | _ => pure (ForInStep.yield w)))
          (fun varsWithF => Bind.bind (m := Id)
            (forIn vars true
              (fun v ok =>
                if varsWithF.contains v = true then
                  pure (ForInStep.yield ok)
                else pure (ForInStep.yield false)))
            (fun ok => pure
              (ok, (⟨dj, DB.trimFrameHyps db vars fr.hyps⟩
                : Frame))))))).run
    = _
  rw [show (forIn (m := Id) fr.hyps
      (fmla.foldlVars ∅ HashSet.insert)
      (fun l r =>
        match db.find? l with
        | some (.hyp true f _) =>
            pure (ForInStep.yield (f.foldlVars r HashSet.insert))
        | _ => pure (ForInStep.yield r))) =
    forIn fr.hyps.toList (fmla.foldlVars ∅ HashSet.insert)
      (fun l r =>
        match db.find? l with
        | some (.hyp true f _) =>
            pure (ForInStep.yield (f.foldlVars r HashSet.insert))
        | _ => pure (ForInStep.yield r))
    from (Array.forIn_toList).symm]
  rw [hbody₁, forIn_list_yield_eq_foldl]
  show (Bind.bind (m := Id)
      (forIn fr.dj (#[] : Array DJ)
        (fun v dj =>
          if ((trimVarsOf db fmla fr).contains v.1 &&
              (trimVarsOf db fmla fr).contains v.2) = true then
            pure (ForInStep.yield (dj.push v))
          else pure (ForInStep.yield dj)))
      (fun dj => Bind.bind (m := Id)
        (forIn fr.hyps (∅ : HashSet String)
          (fun l w =>
            match db.find? l with
            | some (.hyp false f _) =>
                if (trimVarsOf db fmla fr).contains
                    (f[1]!.value) = true then
                  pure (ForInStep.yield (w.insert (f[1]!.value)))
                else pure (ForInStep.yield w)
            | _ => pure (ForInStep.yield w)))
        (fun varsWithF => Bind.bind (m := Id)
          (forIn (trimVarsOf db fmla fr) true
            (fun v ok =>
              if varsWithF.contains v = true then
                pure (ForInStep.yield ok)
              else pure (ForInStep.yield false)))
          (fun ok => pure (ok, (⟨dj,
            DB.trimFrameHyps db (trimVarsOf db fmla fr)
              fr.hyps⟩ : Frame)))))).run = _
  rw [show (forIn (m := Id) fr.dj (#[] : Array DJ)
      (fun v dj =>
        if ((trimVarsOf db fmla fr).contains v.1 &&
            (trimVarsOf db fmla fr).contains v.2) = true then
          pure (ForInStep.yield (dj.push v))
        else pure (ForInStep.yield dj))) =
    forIn fr.dj.toList (#[] : Array DJ)
      (fun v dj =>
        if ((trimVarsOf db fmla fr).contains v.1 &&
            (trimVarsOf db fmla fr).contains v.2) = true then
          pure (ForInStep.yield (dj.push v))
        else pure (ForInStep.yield dj))
    from (Array.forIn_toList).symm]
  rw [hbody₂, forIn_list_yield_eq_foldl]
  rw [show (forIn (m := Id) fr.hyps (∅ : HashSet String)
      (fun l w =>
        match db.find? l with
        | some (.hyp false f _) =>
            if (trimVarsOf db fmla fr).contains
                (f[1]!.value) = true then
              pure (ForInStep.yield (w.insert (f[1]!.value)))
            else pure (ForInStep.yield w)
        | _ => pure (ForInStep.yield w))) =
    forIn fr.hyps.toList (∅ : HashSet String)
      (fun l w =>
        match db.find? l with
        | some (.hyp false f _) =>
            if (trimVarsOf db fmla fr).contains
                (f[1]!.value) = true then
              pure (ForInStep.yield (w.insert (f[1]!.value)))
            else pure (ForInStep.yield w)
        | _ => pure (ForInStep.yield w))
    from (Array.forIn_toList).symm]
  rw [hbody₃, forIn_list_yield_eq_foldl]
  show (Bind.bind (m := Id)
      (forIn (trimVarsOf db fmla fr) true
        (fun v ok =>
          if (trimVarsWithFOf db (trimVarsOf db fmla fr)
              fr).contains v = true then
            pure (ForInStep.yield ok)
          else pure (ForInStep.yield false)))
      (fun ok => pure (ok,
        (⟨trimDJOf (trimVarsOf db fmla fr) fr.dj,
          DB.trimFrameHyps db (trimVarsOf db fmla fr) fr.hyps⟩
            : Frame)))).run = _
  rw [Std.HashSet.forIn_eq_forIn_toList]
  rw [hbody₄, forIn_list_yield_eq_foldl]
  rfl

/-- Tagged names are exactly the variable symbols. -/
theorem mem_taggedVariableNames_iff :
    ∀ {body : List Metamath.Verify.Sym} {v : String},
      v ∈ taggedVariableNames body ↔ Metamath.Verify.Sym.var v ∈ body
  | [], v => by simp [taggedVariableNames]
  | .const c :: rest, v => by
      show v ∈ taggedVariableNames rest ↔ _
      rw [mem_taggedVariableNames_iff]
      simp
  | .var w :: rest, v => by
      show v ∈ w :: taggedVariableNames rest ↔ _
      rw [List.mem_cons, mem_taggedVariableNames_iff]
      simp

theorem toRuntime_toList_tail (formula : ConstantHeadedFormula) :
    formula.toRuntime.toList.tail = formula.body := by
  show ((Metamath.Verify.Sym.const formula.typecode ::
    formula.body).toArray).toList.tail = _
  rw [List.toList_toArray]
  rfl

private theorem foldl_insertVars_contains_iff (v : String) :
    ∀ (ls : List Metamath.Verify.Sym) (acc : HashSet String),
      ((ls.foldl (fun a s =>
        match s with
        | Metamath.Verify.Sym.var w => a.insert w
        | _ => a) acc).contains v = true) ↔
      (Metamath.Verify.Sym.var v ∈ ls ∨ acc.contains v = true)
  | [], acc => by simp
  | s :: rest, acc => by
      rw [List.foldl_cons]
      cases s with
      | const c =>
          show ((rest.foldl _ acc).contains v = true) ↔ _
          rw [foldl_insertVars_contains_iff v rest acc]
          simp
      | var w =>
          show ((rest.foldl _ (acc.insert w)).contains v = true) ↔ _
          rw [foldl_insertVars_contains_iff v rest (acc.insert w)]
          rw [Std.HashSet.contains_insert]
          constructor
          · rintro (hmem | h)
            · exact Or.inl (List.mem_cons_of_mem _ hmem)
            · rcases (Bool.or_eq_true _ _).mp h with heq | hacc
              · exact Or.inl (by
                  have : w = v := by simpa using heq
                  subst this
                  simp)
              · exact Or.inr hacc
          · rintro (hmem | hacc)
            · rcases List.mem_cons.mp hmem with heq | hmem'
              · refine Or.inr ((Bool.or_eq_true _ _).mpr
                  (Or.inl ?_))
                have hvw : v = w := by
                  simpa using heq
                simp [hvw]
              · exact Or.inl hmem'
            · exact Or.inr ((Bool.or_eq_true _ _).mpr (Or.inr hacc))

/-- `foldlVars` accumulates exactly the tagged variables. -/
theorem foldlVars_contains_iff (f : Metamath.Verify.Formula)
    (acc : HashSet String) (v : String) :
    ((f.foldlVars acc HashSet.insert).contains v = true) ↔
      (Metamath.Verify.Sym.var v ∈ f.toList.tail ∨
        acc.contains v = true) := by
  have h_fold : f.foldlVars acc HashSet.insert =
      (f.toList.tail).foldl
        (fun a s => match s with
          | Metamath.Verify.Sym.var w => HashSet.insert a w
          | _ => a) acc := by
    unfold Metamath.Verify.Formula.foldlVars
    have h := (_root_.List.ArrayListExt.Array.foldl_eq_list_foldl_drop
      (arr := f) (init := acc) (start := 1)
      (f := fun a s => match s with
        | Metamath.Verify.Sym.var w => HashSet.insert a w
        | _ => a))
    simp only [List.drop_one] at h
    exact h
  rw [h_fold]
  exact foldl_insertVars_contains_iff v (f.toList.tail) acc

private theorem trimVars_fold_contains_iff (db : RuntimeDB)
    (v : String) :
    ∀ (labels : List String) (acc : HashSet String),
      ((labels.foldl (fun vars l =>
        match db.find? l with
        | some (.hyp true f _) => f.foldlVars vars HashSet.insert
        | _ => vars) acc).contains v = true) ↔
      ((∃ l ∈ labels, ∃ f e,
          db.find? l = some (.hyp true f e) ∧
          Metamath.Verify.Sym.var v ∈ f.toList.tail) ∨
        acc.contains v = true)
  | [], acc => by simp
  | l :: rest, acc => by
      rw [List.foldl_cons]
      cases hfind : db.find? l with
      | none =>
          show ((rest.foldl _ acc).contains v = true) ↔ _
          rw [trimVars_fold_contains_iff db v rest acc]
          constructor
          · rintro (⟨l', hl', hrest⟩ | hacc)
            · exact Or.inl ⟨l', List.mem_cons_of_mem _ hl', hrest⟩
            · exact Or.inr hacc
          · rintro (⟨l', hl', f, e, hfind', hv⟩ | hacc)
            · rcases List.mem_cons.mp hl' with rfl | hl''
              · rw [hfind] at hfind'
                exact nomatch hfind'
              · exact Or.inl ⟨l', hl'', f, e, hfind', hv⟩
            · exact Or.inr hacc
      | some obj =>
          cases obj with
          | hyp ess f e =>
              cases ess with
              | true =>
                  show ((rest.foldl _
                    (f.foldlVars acc HashSet.insert)).contains v =
                      true) ↔ _
                  rw [trimVars_fold_contains_iff db v rest _,
                    foldlVars_contains_iff]
                  constructor
                  · rintro (⟨l', hl', hrest⟩ | hv | hacc)
                    · exact Or.inl ⟨l',
                        List.mem_cons_of_mem _ hl', hrest⟩
                    · exact Or.inl ⟨l, by simp, f, e, hfind, hv⟩
                    · exact Or.inr hacc
                  · rintro (⟨l', hl', f', e', hfind', hv⟩ | hacc)
                    · rcases List.mem_cons.mp hl' with rfl | hl''
                      · rw [hfind] at hfind'
                        obtain ⟨rfl, rfl⟩ :
                            f' = f ∧ e' = e := by
                          simpa using hfind'.symm
                        exact Or.inr (Or.inl hv)
                      · exact Or.inl ⟨l', hl'', f', e', hfind', hv⟩
                    · exact Or.inr (Or.inr hacc)
              | false =>
                  show ((rest.foldl _ acc).contains v = true) ↔ _
                  rw [trimVars_fold_contains_iff db v rest acc]
                  constructor
                  · rintro (⟨l', hl', hrest⟩ | hacc)
                    · exact Or.inl ⟨l',
                        List.mem_cons_of_mem _ hl', hrest⟩
                    · exact Or.inr hacc
                  · rintro (⟨l', hl', f', e', hfind', hv⟩ | hacc)
                    · rcases List.mem_cons.mp hl' with rfl | hl''
                      · rw [hfind] at hfind'
                        exact nomatch (by
                          simpa using hfind'.symm :
                            f' = f ∧ False ∧ e' = e).2.1
                      · exact Or.inl ⟨l', hl'', f', e', hfind', hv⟩
                    · exact Or.inr hacc
          | const c =>
              show ((rest.foldl _ acc).contains v = true) ↔ _
              rw [trimVars_fold_contains_iff db v rest acc]
              constructor
              · rintro (⟨l', hl', hrest⟩ | hacc)
                · exact Or.inl ⟨l', List.mem_cons_of_mem _ hl',
                    hrest⟩
                · exact Or.inr hacc
              · rintro (⟨l', hl', f', e', hfind', hv⟩ | hacc)
                · rcases List.mem_cons.mp hl' with rfl | hl''
                  · rw [hfind] at hfind'
                    exact nomatch hfind'
                  · exact Or.inl ⟨l', hl'', f', e', hfind', hv⟩
                · exact Or.inr hacc
          | var w =>
              show ((rest.foldl _ acc).contains v = true) ↔ _
              rw [trimVars_fold_contains_iff db v rest acc]
              constructor
              · rintro (⟨l', hl', hrest⟩ | hacc)
                · exact Or.inl ⟨l', List.mem_cons_of_mem _ hl',
                    hrest⟩
                · exact Or.inr hacc
              · rintro (⟨l', hl', f', e', hfind', hv⟩ | hacc)
                · rcases List.mem_cons.mp hl' with rfl | hl''
                  · rw [hfind] at hfind'
                    exact nomatch hfind'
                  · exact Or.inl ⟨l', hl'', f', e', hfind', hv⟩
                · exact Or.inr hacc
          | assert f fr e =>
              show ((rest.foldl _ acc).contains v = true) ↔ _
              rw [trimVars_fold_contains_iff db v rest acc]
              constructor
              · rintro (⟨l', hl', hrest⟩ | hacc)
                · exact Or.inl ⟨l', List.mem_cons_of_mem _ hl',
                    hrest⟩
                · exact Or.inr hacc
              · rintro (⟨l', hl', f', e', hfind', hv⟩ | hacc)
                · rcases List.mem_cons.mp hl' with rfl | hl''
                  · rw [hfind] at hfind'
                    exact nomatch hfind'
                  · exact Or.inl ⟨l', hl'', f', e', hfind', hv⟩
                · exact Or.inr hacc

/-- Under agreement the trim variable set is exactly the source
mandatory-variable set. -/
theorem contains_trimVarsOf_iff {db : RuntimeDB}
    {before : SourceState}
    (agreement : RuntimeDBAgrees db before)
    (formula : ConstantHeadedFormula) (v : String) :
    ((trimVarsOf db formula.toRuntime db.frame).contains v = true) ↔
      v ∈ mandatoryVariableNames before formula := by
  have hpoint : ∀ hyp ∈ before.activeHypotheses,
      projectHypothesis? db hyp.label = some hyp :=
    fun hyp hh => activeHyp_project_self agreement hyp hh
  unfold trimVarsOf
  rw [trimVars_fold_contains_iff, foldlVars_contains_iff,
    mem_mandatoryVariableNames_iff]
  constructor
  · rintro (⟨l, hl, f, e, hfind, hv⟩ | hv | hemp)
    · rw [agreement.rawFrame.2] at hl
      obtain ⟨hyp, hhyp, rfl⟩ := List.mem_map.mp hl
      obtain ⟨rf, hfind', hform, -⟩ :=
        projectHypothesis?_eq_some_fidelity db hyp.label hyp
          (hpoint hyp hhyp)
      rw [hfind'] at hfind
      have hinj := Option.some.inj hfind
      cases hyp with
      | floating lbl tc w =>
          simp [hypothesisEssentialBit] at hinj
      | essential lbl f0 =>
          have hrf : rf = f0.toRuntime :=
            (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
              simpa [HypothesisView.formula] using hform)
          have hf : f = rf := by
            have := congrArg (fun o =>
              match o with
              | Metamath.Verify.Object.hyp _ ff _ => ff
              | _ => f) hinj
            simpa using this.symm
          refine Or.inr ⟨lbl, f0, hhyp, ?_⟩
          rw [mem_taggedVariableNames_iff]
          rw [hf, hrf, toRuntime_toList_tail] at hv
          exact hv
    · refine Or.inl ?_
      rw [toRuntime_toList_tail] at hv
      rw [mem_taggedVariableNames_iff]
      exact hv
    · simp at hemp
  · rintro (hv | ⟨label, f0, hmem, hv⟩)
    · refine Or.inr (Or.inl ?_)
      rw [toRuntime_toList_tail]
      rw [mem_taggedVariableNames_iff] at hv
      exact hv
    · refine Or.inl ?_
      obtain ⟨rf, hfind', hform, -⟩ :=
        projectHypothesis?_eq_some_fidelity db
          (HypothesisView.essential label f0).label
          (.essential label f0) (hpoint _ hmem)
      have hrf : rf = f0.toRuntime :=
        (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
          simpa [HypothesisView.formula] using hform)
      refine ⟨label, ?_, rf, label, ?_, ?_⟩
      · rw [agreement.rawFrame.2]
        exact List.mem_map.mpr ⟨.essential label f0, hmem, rfl⟩
      · rw [show (HypothesisView.essential label f0).label = label
          from rfl] at hfind'
        exact hfind'
      · rw [hrf, toRuntime_toList_tail]
        rw [mem_taggedVariableNames_iff] at hv
        exact hv

private theorem toList_trimDJOf_fold (vars : HashSet String) :
    ∀ (pairs : List Metamath.Verify.DJ)
      (acc : Array Metamath.Verify.DJ),
      (pairs.foldl (fun acc v =>
        if (vars.contains v.1 && vars.contains v.2) = true then
          acc.push v
        else acc) acc).toList =
      acc.toList ++ pairs.filter
        (fun v => vars.contains v.1 && vars.contains v.2)
  | [], acc => by simp
  | v :: rest, acc => by
      rw [List.foldl_cons]
      by_cases h : (vars.contains v.1 && vars.contains v.2) = true
      · rw [if_pos h, toList_trimDJOf_fold vars rest _,
          show (v :: rest).filter
              (fun v => vars.contains v.1 && vars.contains v.2) =
            v :: rest.filter
              (fun v => vars.contains v.1 && vars.contains v.2)
            from by rw [List.filter_cons]; simp [h],
          Array.toList_push]
        simp
      · rw [if_neg h, toList_trimDJOf_fold vars rest acc,
          show (v :: rest).filter
              (fun v => vars.contains v.1 && vars.contains v.2) =
            rest.filter
              (fun v => vars.contains v.1 && vars.contains v.2)
            from by rw [List.filter_cons]; simp [h]]

/-- Under agreement the trimmed disjointness pairs are exactly the
source mandatory frame's pairs. -/
theorem trimDJOf_eq_mandatory {db : RuntimeDB}
    {before : SourceState}
    (agreement : RuntimeDBAgrees db before)
    (formula : ConstantHeadedFormula) :
    (trimDJOf (trimVarsOf db formula.toRuntime db.frame)
        db.frame.dj).toList =
      (mandatoryFrame before formula).distinctVariables := by
  unfold trimDJOf
  rw [toList_trimDJOf_fold]
  rw [show (#[] : Array Metamath.Verify.DJ).toList = [] from rfl,
    List.nil_append, agreement.rawFrame.1]
  show _ = before.activeDistinctVariables.filter
    (fun pair =>
      (mandatoryVariableNames before formula).contains pair.1 &&
        (mandatoryVariableNames before formula).contains pair.2)
  apply List.filter_congr
  intro pair hmem
  have h1 := contains_trimVarsOf_iff agreement formula pair.1
  have h2 := contains_trimVarsOf_iff agreement formula pair.2
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true]
  rw [h1, h2, List.contains_eq_mem, List.contains_eq_mem]
  simp

private theorem trimFrameHypsPairsList_map_snd
    (db : RuntimeDB) (vars : HashSet String) :
    ∀ (ls : List String) (i : Nat),
      ((DB.trimFrameHypsPairsList db vars i ls).map
        (fun p => p.2)) =
        ls.filter (fun l => db.trimFrameKeep vars l)
  | [], i => rfl
  | l :: rest, i => by
      have ih := trimFrameHypsPairsList_map_snd db vars rest (i + 1)
      unfold DB.trimFrameHypsPairsList at ih ⊢
      rw [List.zipIdx_cons]
      by_cases h : db.trimFrameKeep vars l = true <;>
        simp [h, ih]

theorem toList_trimFrameHyps (db : RuntimeDB)
    (vars : HashSet String) (hyps : Array String) :
    (DB.trimFrameHyps db vars hyps).toList =
      hyps.toList.filter (fun l => db.trimFrameKeep vars l) := by
  unfold DB.trimFrameHyps DB.trimFrameHypsPairs
  rw [show ((DB.trimFrameHypsPairsList db vars 0
      hyps.toList).toArray.map (fun p => p.2)) =
    ((DB.trimFrameHypsPairsList db vars 0 hyps.toList).map
      (fun p => p.2)).toArray from by simp]
  rw [List.toList_toArray]
  exact trimFrameHypsPairsList_map_snd db vars hyps.toList 0

/-- The mandatory-hypothesis keep decision as a function. -/
def mandatoryKeep (state : SourceState)
    (formula : ConstantHeadedFormula) : HypothesisView → Bool
  | .floating _ _ variableName =>
      (mandatoryVariableNames state formula).contains variableName
  | .essential _ _ => true

private theorem trimFrameKeep_of_view {db : RuntimeDB}
    {before : SourceState}
    (agreement : RuntimeDBAgrees db before)
    (formula : ConstantHeadedFormula) {hyp : HypothesisView}
    (hmem : hyp ∈ before.activeHypotheses) :
    db.trimFrameKeep (trimVarsOf db formula.toRuntime db.frame)
        hyp.label =
      mandatoryKeep before formula hyp := by
  obtain ⟨rf, hfind, hform, -⟩ :=
    projectHypothesis?_eq_some_fidelity db hyp.label hyp
      (activeHyp_project_self agreement hyp hmem)
  unfold DB.trimFrameKeep
  rw [hfind]
  cases hyp with
  | essential l f => rfl
  | floating l tc w =>
      have hrf : rf = (⟨tc, [.var w]⟩ :
          ConstantHeadedFormula).toRuntime :=
        (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
          simpa [HypothesisView.formula] using hform)
      subst hrf
      show (trimVarsOf db formula.toRuntime db.frame).contains
        ((⟨tc, [.var w]⟩ :
          ConstantHeadedFormula).toRuntime[1]!.value) =
        (mandatoryVariableNames before formula).contains w
      rw [show ((⟨tc, [.var w]⟩ :
          ConstantHeadedFormula).toRuntime[1]!.value) = w from by
        simp [ConstantHeadedFormula.toRuntime,
          Metamath.Verify.Sym.value]]
      rw [Bool.eq_iff_iff, contains_trimVarsOf_iff agreement formula,
        List.contains_eq_mem]
      simp

/-- Under agreement the trimmed hypothesis labels are exactly the
source mandatory hypotheses' labels. -/
theorem trimFrameHyps_eq_mandatory {db : RuntimeDB}
    {before : SourceState}
    (agreement : RuntimeDBAgrees db before)
    (formula : ConstantHeadedFormula) :
    DB.trimFrameHyps db (trimVarsOf db formula.toRuntime db.frame)
        db.frame.hyps =
      ((mandatoryHypotheses before formula).map
        HypothesisView.label).toArray := by
  apply Array.ext'
  rw [toList_trimFrameHyps, List.toList_toArray,
    agreement.rawFrame.2, mandatoryHypotheses_eq_filter,
    List.filter_map]
  congr 1
  apply List.filter_congr
  intro hyp hmem
  have hkeep := trimFrameKeep_of_view agreement formula hmem
  show db.trimFrameKeep (trimVarsOf db formula.toRuntime db.frame)
    hyp.label = _
  rw [hkeep]
  cases hyp with
  | floating l tc w => rfl
  | essential l f => rfl

/-- Frame-respect components cover every mandatory variable with a
mandatory floating hypothesis. -/
theorem mandatory_vars_covered {before : SourceState}
    {formula : ConstantHeadedFormula}
    (hrespect : formulaSymbolsRespectFrame
      (floatingVariableNames (mandatoryHypotheses before formula))
      formula = true)
    (hhyps : ∀ hyp ∈ mandatoryHypotheses before formula,
      formulaSymbolsRespectFrame
        (floatingVariableNames (mandatoryHypotheses before formula))
        hyp.formula = true) :
    ∀ v ∈ mandatoryVariableNames before formula,
      v ∈ floatingVariableNames
        (mandatoryHypotheses before formula) := by
  intro v hv
  rcases mem_mandatoryVariableNames_iff.mp hv with hform | ⟨label, f,
    hmem, hvf⟩
  · rw [formulaSymbolsRespectFrame, List.all_eq_true] at hrespect
    have := hrespect (.var v) (mem_taggedVariableNames_iff.mp hform)
    rw [show symbolRespectsFrame
        (floatingVariableNames (mandatoryHypotheses before formula))
        (.var v) =
      (floatingVariableNames
        (mandatoryHypotheses before formula)).contains v
      from rfl, List.contains_eq_mem, decide_eq_true_iff] at this
    exact this
  · have hmemM : HypothesisView.essential label f ∈
        mandatoryHypotheses before formula := by
      rw [mandatoryHypotheses_eq_filter]
      exact List.mem_filter.mpr ⟨hmem, rfl⟩
    have hresp := hhyps _ hmemM
    rw [formulaSymbolsRespectFrame, List.all_eq_true] at hresp
    have := hresp (.var v) (by
      show Metamath.Verify.Sym.var v ∈
        (HypothesisView.essential label f).formula.body
      exact mem_taggedVariableNames_iff.mp hvf)
    rw [show symbolRespectsFrame
        (floatingVariableNames (mandatoryHypotheses before formula))
        (.var v) =
      (floatingVariableNames
        (mandatoryHypotheses before formula)).contains v
      from rfl, List.contains_eq_mem, decide_eq_true_iff] at this
    exact this

private theorem trimVarsWithF_fold_preserves (db : RuntimeDB)
    (vars : HashSet String) {v : String} :
    ∀ (labels : List String) (acc : HashSet String),
      acc.contains v = true →
      ((labels.foldl (fun acc l =>
        match db.find? l with
        | some (.hyp false f _) =>
            if vars.contains (f[1]!.value) = true then
              acc.insert (f[1]!.value)
            else acc
        | _ => acc) acc).contains v = true)
  | [], acc, h => h
  | l :: rest, acc, h => by
      rw [List.foldl_cons]
      cases hfind : db.find? l with
      | none =>
          exact trimVarsWithF_fold_preserves db vars rest acc h
      | some obj =>
          cases obj with
          | hyp ess f e =>
              cases ess with
              | false =>
                  by_cases hc : vars.contains (f[1]!.value) = true
                  · show ((rest.foldl _
                      (if vars.contains (f[1]!.value) = true then
                        acc.insert (f[1]!.value)
                      else acc)).contains v = true)
                    rw [if_pos hc]
                    refine trimVarsWithF_fold_preserves db vars
                      rest _ ?_
                    rw [Std.HashSet.contains_insert]
                    simp [h]
                  · show ((rest.foldl _
                      (if vars.contains (f[1]!.value) = true then
                        acc.insert (f[1]!.value)
                      else acc)).contains v = true)
                    rw [if_neg hc]
                    exact trimVarsWithF_fold_preserves db vars
                      rest acc h
              | true =>
                  exact trimVarsWithF_fold_preserves db vars
                    rest acc h
          | const c =>
              exact trimVarsWithF_fold_preserves db vars rest acc h
          | var w =>
              exact trimVarsWithF_fold_preserves db vars rest acc h
          | assert f fr e =>
              exact trimVarsWithF_fold_preserves db vars rest acc h

private theorem trimVarsWithF_fold_of_witness (db : RuntimeDB)
    (vars : HashSet String) {v : String} :
    ∀ (labels : List String) (acc : HashSet String),
      (∃ l ∈ labels, ∃ f e,
        db.find? l = some (.hyp false f e) ∧
        f[1]!.value = v ∧ vars.contains v = true) →
      ((labels.foldl (fun acc l =>
        match db.find? l with
        | some (.hyp false f _) =>
            if vars.contains (f[1]!.value) = true then
              acc.insert (f[1]!.value)
            else acc
        | _ => acc) acc).contains v = true)
  | [], acc, h => by
      obtain ⟨l, hl, -⟩ := h
      exact absurd hl (List.not_mem_nil)
  | l :: rest, acc, h => by
      obtain ⟨l', hl', f, e, hfind, hval, hvc⟩ := h
      rcases List.mem_cons.mp hl' with rfl | hl''
      · rw [List.foldl_cons, hfind]
        show ((rest.foldl _
          (if vars.contains (f[1]!.value) = true then
            acc.insert (f[1]!.value)
          else acc)).contains v = true)
        rw [hval, if_pos hvc]
        refine trimVarsWithF_fold_preserves db vars rest _ ?_
        rw [Std.HashSet.contains_insert]
        simp
      · rw [List.foldl_cons]
        exact trimVarsWithF_fold_of_witness db vars rest _
          ⟨l', hl'', f, e, hfind, hval, hvc⟩

private theorem foldl_guard_true_of_all
    (varsWithF : HashSet String) :
    ∀ (ls : List String),
      (∀ v ∈ ls, varsWithF.contains v = true) →
      ls.foldl (fun ok v =>
        if varsWithF.contains v = true then ok else false) true =
        true
  | [], _ => rfl
  | v :: rest, h => by
      rw [List.foldl_cons, if_pos (h v (by simp))]
      exact foldl_guard_true_of_all varsWithF rest
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- Under agreement and mandatory-float coverage, the trim
float-coverage check passes. -/
theorem trimOkOf_eq_true {db : RuntimeDB} {before : SourceState}
    (agreement : RuntimeDBAgrees db before)
    (formula : ConstantHeadedFormula)
    (hcover : ∀ v ∈ mandatoryVariableNames before formula,
      v ∈ floatingVariableNames
        (mandatoryHypotheses before formula)) :
    trimOkOf (trimVarsOf db formula.toRuntime db.frame)
      (trimVarsWithFOf db
        (trimVarsOf db formula.toRuntime db.frame) db.frame) =
      true := by
  unfold trimOkOf
  apply foldl_guard_true_of_all
  intro v hv
  have hvc : (trimVarsOf db formula.toRuntime db.frame).contains v =
      true := by
    exact Std.HashSet.mem_iff_contains.mp
      (Std.HashSet.mem_toList.mp hv)
  have hmand := (contains_trimVarsOf_iff agreement formula v).mp hvc
  obtain ⟨hyp, hhypM, hfv⟩ := List.mem_filterMap.mp
    (hcover v hmand)
  cases hyp with
  | essential l f => exact nomatch hfv
  | floating l tc w =>
      have hw : w = v := by
        simpa [HypothesisView.floatingVariable?] using hfv
      subst hw
      have hhypA : HypothesisView.floating l tc w ∈
          before.activeHypotheses := by
        rw [mandatoryHypotheses_eq_filter] at hhypM
        exact List.mem_of_mem_filter hhypM
      obtain ⟨rf, hfind, hform, -⟩ :=
        projectHypothesis?_eq_some_fidelity db
          (HypothesisView.floating l tc w).label
          (.floating l tc w)
          (activeHyp_project_self agreement _ hhypA)
      have hrf : rf = (⟨tc, [.var w]⟩ :
          ConstantHeadedFormula).toRuntime :=
        (ConstantHeadedFormula.ofRuntime?_eq_some_iff _ _).mp (by
          simpa [HypothesisView.formula] using hform)
      subst hrf
      unfold trimVarsWithFOf
      apply trimVarsWithF_fold_of_witness
      refine ⟨l, ?_, (⟨tc, [.var w]⟩ :
        ConstantHeadedFormula).toRuntime, l, ?_, ?_, hvc⟩
      · rw [agreement.rawFrame.2]
        exact List.mem_map.mpr ⟨.floating l tc w, hhypA, rfl⟩
      · rw [show (HypothesisView.floating l tc w).label = l
          from rfl] at hfind
        exact hfind
      · simp [ConstantHeadedFormula.toRuntime,
          Metamath.Verify.Sym.value]

private theorem trimFrame'_ok_iff {db : RuntimeDB}
    {fmla : Metamath.Verify.Formula} {fr : RuntimeFrame} :
    db.trimFrame' fmla = .ok fr ↔
      db.trimFrame fmla = (true, fr) := by
  unfold DB.trimFrame'
  obtain ⟨ok, fr'⟩ := db.trimFrame fmla
  cases ok
  · simp
  · simp [pure, Except.pure]

/-- **The mandatory-frame bridge**: under agreement and mandatory
float coverage, the shipped trim produces exactly the source
mandatory frame. -/
theorem trimFrame'_eq_mandatory {db : RuntimeDB}
    {before : SourceState}
    (agreement : RuntimeDBAgrees db before)
    (formula : ConstantHeadedFormula)
    (hcover : ∀ v ∈ mandatoryVariableNames before formula,
      v ∈ floatingVariableNames
        (mandatoryHypotheses before formula)) :
    db.trimFrame' formula.toRuntime =
      .ok (mandatoryFrame before formula).toRuntime := by
  rw [trimFrame'_ok_iff, trimFrame_eq_functional]
  rw [Prod.mk.injEq]
  refine ⟨trimOkOf_eq_true agreement formula hcover, ?_⟩
  rw [show (mandatoryFrame before formula).toRuntime =
    (⟨(mandatoryFrame before formula).distinctVariables.toArray,
      (mandatoryFrame before formula).hypothesisLabels.toArray⟩
        : RuntimeFrame) from rfl]
  refine congrArg₂ Metamath.Verify.Frame.mk ?_ ?_
  · apply Array.ext'
    rw [trimDJOf_eq_mandatory agreement formula,
      List.toList_toArray]
  · rw [trimFrameHyps_eq_mandatory agreement formula]
    rfl

/-- An accepted assertion insertion certifies mandatory-float
coverage. -/
theorem mandatory_covered_of_insert {before after : SourceState}
    {label : String} {formula : ConstantHeadedFormula}
    (hdecl : insertAssertion? before label formula = some after) :
    ∀ v ∈ mandatoryVariableNames before formula,
      v ∈ floatingVariableNames
        (mandatoryHypotheses before formula) := by
  have hvalid : sourceStateValid after = true :=
    insertAssertion?_valid hdecl
  have hshape := insertAssertion?_eq_some_shape hdecl
  have hpv := sourcePrefixValid_of_sourceStateValid after hvalid
  simp only [sourcePrefixValid, Bool.and_eq_true,
    SourceState.toSourcePrefix] at hpv
  have hall := hpv.1.2
  rw [List.all_eq_true] at hall
  have hmem : sourceAssertion before label formula ∈
      after.assertions := by
    rw [hshape.1]
    exact List.mem_append_right _ (by simp)
  have hav := hall _ hmem
  rw [sourceAssertionValid] at hav
  simp only [Bool.and_eq_true] at hav
  have hrespect : formulaSymbolsRespectFrame
      (floatingVariableNames (mandatoryHypotheses before formula))
      formula = true := by
    have h := hav.1.1.2
    exact h
  have hframe : sourceFrameValid
      (sourceAssertion before label formula).frame
      (sourceAssertion before label formula).hypotheses = true :=
    hav.1.1.1
  rw [sourceFrameValid] at hframe
  simp only [Bool.and_eq_true] at hframe
  have hhyps : ∀ hyp ∈ mandatoryHypotheses before formula,
      formulaSymbolsRespectFrame
        (floatingVariableNames (mandatoryHypotheses before formula))
        hyp.formula = true := by
    have h := hframe.1.2
    rw [List.all_eq_true] at h
    intro hyp hmem'
    exact h hyp hmem'
  exact mandatory_vars_covered hrespect hhyps

/-- The shipped `$a` operation reduces to the discharged assert
insertion on the accepted path. -/
theorem insertAxiom_eq_insert {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (hdecl : insertAssertion? before label formula = some after)
    (hint : db.interrupt = false) (pos : Pos) :
    db.insertAxiom pos label formula.toRuntime =
      db.insert pos label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime) := by
  unfold DB.insertAxiom
  simp only [toRuntime_hasConstHead, DB.error, agreement.errorFree,
    if_true]
  rw [trimFrame'_eq_mandatory agreement formula
    (mandatory_covered_of_insert hdecl)]
  simp [hint]

/-- **`$a` statement co-evolution against the shipped operation.** -/
theorem RuntimeDBAgrees.declareAxiom' {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (hdecl : declareAxiom? before label formula = some after)
    (hint : db.interrupt = false) (pos : Pos) :
    RuntimeDBAgrees
      (db.insertAxiom pos label formula.toRuntime) after := by
  have hdecl' : insertAssertion? before label formula =
      some after := hdecl
  rw [insertAxiom_eq_insert agreement hdecl' hint pos]
  exact RuntimeDBAgrees.insertAssertion agreement hdecl' pos

end TrimLane

/-! ## The payload dispatcher and whole-fold co-evolution

One runtime operation per source payload, all in shipped vocabulary.
The whole-fold theorem grows both worlds from their initial states with
no supplied premise: the interrupt flag is false initially and no
shipped operation ever sets it. -/

section FoldLane

open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4

/-- The shipped runtime operation selected by a source payload. -/
def runtimeApplyPayload (pos : Pos) (payload : LocalPayload)
    (db : RuntimeDB) : RuntimeDB :=
  match payload with
  | .openScope => db.pushScope
  | .closeScope => db.popScope pos
  | .declareConstants names =>
      names.foldl (fun d n => d.insert pos n (fun l => .const l)) db
  | .declareVariables names =>
      names.foldl (fun d n => d.insert pos n (fun l => .var l)) db
  | .declareDisjoint names =>
      (allDistinctDJ names).foldl
        (fun d p => d.withDJ (fun dj => dj.push p)) db
  | .declareFloating label typecode variableName =>
      db.insertHyp pos label false
        ((⟨typecode, [.var variableName]⟩ :
          ConstantHeadedFormula).toRuntime)
  | .declareEssential label formula =>
      db.insertHyp pos label true formula.toRuntime
  | .declareAxiom label formula =>
      db.insertAxiom pos label formula.toRuntime
  | .completeBlock => db

private theorem insert_interrupt (db : RuntimeDB) (pos : Pos)
    (l : String) (obj : String → Metamath.Verify.Object) :
    (db.insert pos l obj).interrupt = db.interrupt := by
  unfold DB.insert
  dsimp only []
  repeat' split
  all_goals rfl

/-- Shipped object insertion preserves the external interrupt flag. -/
theorem runtimeInsert_interrupt (db : RuntimeDB) (pos : Pos)
    (l : String) (obj : String → Metamath.Verify.Object) :
    (db.insert pos l obj).interrupt = db.interrupt :=
  insert_interrupt db pos l obj

/-- A successful shipped object insertion is independent of the diagnostic
position supplied to it.  Positions occur only in rejected results; the
accepted database update stores no source location. -/
theorem runtimeInsert_eq_of_errorFree (db : RuntimeDB) (left right : Pos)
    (label : String) (obj : String → Metamath.Verify.Object)
    (success : (db.insert left label obj).error? = none) :
    db.insert left label obj = db.insert right label obj := by
  cases objectShape : obj label with
  | const constantName =>
      by_cases scopeGate :
          db.config.allowConstInnerScope = false ∧ 0 < db.scopes.size
      · simp [DB.insert, objectShape, scopeGate, DB.mkErrorFromEvidence,
          DB.mkErrorWithEvidence, DB.error] at success
      ·
        by_cases existingError : db.error = true
        · simp [DB.insert, objectShape, scopeGate, existingError]
        ·
          cases existingObject : db.find? label with
          | none =>
              simp [DB.insert, objectShape, scopeGate, existingError,
                existingObject]
          | some existing =>
              cases existing with
              | var variableName =>
                  simp [DB.insert, objectShape, scopeGate, existingError,
                    existingObject, DB.mkErrorFromEvidence,
                    DB.mkErrorWithEvidence] at success
              | const existingName =>
                  simp [DB.insert, objectShape, scopeGate, existingError,
                    existingObject, DB.mkErrorFromEvidence,
                    DB.mkErrorWithEvidence] at success
              | hyp essential formula hypothesisLabel =>
                  simp [DB.insert, objectShape, scopeGate, existingError,
                    existingObject, DB.mkErrorFromEvidence,
                    DB.mkErrorWithEvidence] at success
              | assert formula frame assertionLabel =>
                  simp [DB.insert, objectShape, scopeGate, existingError,
                    existingObject, DB.mkErrorFromEvidence,
                    DB.mkErrorWithEvidence] at success
  | var variableName =>
      by_cases existingError : db.error = true
      · simp [DB.insert, objectShape, existingError]
      · cases existingObject : db.find? label with
        | none => simp [DB.insert, objectShape, existingError, existingObject]
        | some existing =>
            cases existing with
            | var existingName =>
                simp [DB.insert, objectShape, existingError, existingObject]
            | const existingName =>
                simp [DB.insert, objectShape, existingError, existingObject,
                  DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at success
            | hyp essential formula hypothesisLabel =>
                simp [DB.insert, objectShape, existingError, existingObject,
                  DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at success
            | assert formula frame assertionLabel =>
                simp [DB.insert, objectShape, existingError, existingObject,
                  DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at success
  | hyp essential formula hypothesisLabel =>
      by_cases existingError : db.error = true
      · simp [DB.insert, objectShape, existingError]
      · cases existingObject : db.find? label with
        | none => simp [DB.insert, objectShape, existingError, existingObject]
        | some existing =>
            cases existing <;>
              simp [DB.insert, objectShape, existingError, existingObject,
                DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at success
  | assert formula frame assertionLabel =>
      by_cases existingError : db.error = true
      · simp [DB.insert, objectShape, existingError]
      · cases existingObject : db.find? label with
        | none => simp [DB.insert, objectShape, existingError, existingObject]
        | some existing =>
            cases existing <;>
              simp [DB.insert, objectShape, existingError, existingObject,
                DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at success

private theorem withHyps_interrupt (db : RuntimeDB)
    (g : Array String → Array String) :
    (db.withHyps g).interrupt = db.interrupt := by
  unfold Metamath.Verify.DB.withHyps Metamath.Verify.DB.withFrame
  rcases hfr : db.frame with ⟨dj, hyps⟩
  rfl

private theorem insertHyp_interrupt (db : RuntimeDB) (pos : Pos)
    (l : String) (ess : Bool) (f : Metamath.Verify.Formula) :
    (db.insertHyp pos l ess f).interrupt = db.interrupt := by
  unfold DB.insertHyp
  dsimp only []
  set d₁ := db.insertHypChecks pos ess f with hd₁
  have h₁ : d₁.interrupt = db.interrupt := by
    rw [hd₁]
    unfold DB.insertHypChecks
    dsimp only []
    repeat' split
    all_goals rfl
  split
  · exact h₁
  · set d₂ := d₁.insert pos l (.hyp ess f) with hd₂
    have h₂ : d₂.interrupt = db.interrupt := by
      rw [hd₂, insert_interrupt]
      exact h₁
    split
    · exact h₂
    · rw [withHyps_interrupt]
      exact h₂

private theorem insertAxiom_interrupt (db : RuntimeDB) (pos : Pos)
    (l : String) (f : Metamath.Verify.Formula) :
    (db.insertAxiom pos l f).interrupt = db.interrupt := by
  unfold DB.insertAxiom
  dsimp only []
  set d₁ := (if f.hasConstHead = true then db else
    DB.mkErrorFromEvidence db pos
      (.scopeDecl .firstSymbolNotConstant)) with hd₁
  have h₁ : d₁.interrupt = db.interrupt := by
    rw [hd₁]
    split <;> rfl
  split
  · exact h₁
  · split
    · split
      · exact h₁
      · rw [insert_interrupt]
        exact h₁
    · exact h₁

private theorem withDJ_interrupt (db : RuntimeDB)
    (g : Array Metamath.Verify.DJ → Array Metamath.Verify.DJ) :
    (db.withDJ g).interrupt = db.interrupt := by
  unfold Metamath.Verify.DB.withDJ Metamath.Verify.DB.withFrame
  rcases hfr : db.frame with ⟨dj, hyps⟩
  rfl

private theorem popScope_interrupt (db : RuntimeDB) (pos : Pos) :
    (db.popScope pos).interrupt = db.interrupt := by
  unfold DB.popScope
  split <;> rfl

private theorem foldl_interrupt {α : Type _}
    (step : RuntimeDB → α → RuntimeDB)
    (hstep : ∀ d a, (step d a).interrupt = d.interrupt) :
    ∀ (ls : List α) (db : RuntimeDB),
      (ls.foldl step db).interrupt = db.interrupt
  | [], db => rfl
  | a :: rest, db => by
      rw [List.foldl_cons, foldl_interrupt step hstep rest _,
        hstep]

/-- No shipped operation ever raises the interrupt flag. -/
theorem runtimeApplyPayload_interrupt (pos : Pos)
    (payload : LocalPayload) (db : RuntimeDB) :
    (runtimeApplyPayload pos payload db).interrupt =
      db.interrupt := by
  cases payload with
  | openScope => rfl
  | closeScope => exact popScope_interrupt db pos
  | declareConstants names =>
      exact foldl_interrupt _
        (fun d n => insert_interrupt d pos n _) names db
  | declareVariables names =>
      exact foldl_interrupt _
        (fun d n => insert_interrupt d pos n _) names db
  | declareDisjoint names =>
      exact foldl_interrupt _
        (fun d p => withDJ_interrupt d _) (allDistinctDJ names) db
  | declareFloating label typecode variableName =>
      exact insertHyp_interrupt db pos label false _
  | declareEssential label formula =>
      exact insertHyp_interrupt db pos label true _
  | declareAxiom label formula =>
      exact insertAxiom_interrupt db pos label _
  | completeBlock => rfl

/-- **Per-payload co-evolution**: every accepted source payload is
matched by its shipped runtime operation. -/
theorem RuntimeDBAgrees.applyPayload {db : RuntimeDB}
    {before after : SourceState} {payload : LocalPayload}
    (agreement : RuntimeDBAgrees db before)
    (happly : applyLocalPayload? payload before = some after)
    (hint : db.interrupt = false) (pos : Pos) :
    RuntimeDBAgrees (runtimeApplyPayload pos payload db) after := by
  cases payload with
  | openScope =>
      exact RuntimeDBAgrees.pushScope agreement happly
  | closeScope =>
      exact RuntimeDBAgrees.popScope' agreement pos happly
  | declareConstants names =>
      exact RuntimeDBAgrees.declareConstants' agreement happly pos
  | declareVariables names =>
      exact RuntimeDBAgrees.declareVariables' agreement happly pos
  | declareDisjoint names =>
      exact RuntimeDBAgrees.declareDisjoint'' agreement happly
  | declareFloating label typecode variableName =>
      exact RuntimeDBAgrees.declareFloating' agreement happly pos
  | declareEssential label formula =>
      exact RuntimeDBAgrees.declareEssential' agreement happly pos
  | declareAxiom label formula =>
      exact RuntimeDBAgrees.declareAxiom' agreement happly hint pos
  | completeBlock =>
      exact RuntimeDBAgrees.completeBlock agreement happly

/-- Sequential source payload application. -/
def applyLocalPayloads? : List LocalPayload → SourceState →
    Option SourceState
  | [], state => some state
  | payload :: rest, state => do
      let mid ← applyLocalPayload? payload state
      applyLocalPayloads? rest mid

/-- Accepted payload sequences compose. -/
theorem applyLocalPayloads?_append :
    ∀ {ps₁ ps₂ : List LocalPayload} {s mid fin : SourceState},
      applyLocalPayloads? ps₁ s = some mid →
      applyLocalPayloads? ps₂ mid = some fin →
      applyLocalPayloads? (ps₁ ++ ps₂) s = some fin
  | [], ps₂, s, mid, fin, h₁, h₂ => by
      cases Option.some.inj h₁
      simpa using h₂
  | p :: rest, ps₂, s, mid, fin, h₁, h₂ => by
      rw [show applyLocalPayloads? (p :: rest) s =
        (do
          let m ← applyLocalPayload? p s
          applyLocalPayloads? rest m) from rfl] at h₁
      obtain ⟨m, hm, hrest⟩ := bind_some_inv h₁
      rw [List.cons_append,
        show applyLocalPayloads? (p :: (rest ++ ps₂)) s =
          (do
            let m ← applyLocalPayload? p s
            applyLocalPayloads? (rest ++ ps₂) m) from rfl,
        hm]
      exact applyLocalPayloads?_append hrest h₂

/-- **Whole-fold co-evolution**: agreement is preserved along any
accepted payload sequence. -/
theorem RuntimeDBAgrees.applyPayloads (pos : Pos) :
    ∀ {payloads : List LocalPayload} {db : RuntimeDB}
      {before after : SourceState},
      RuntimeDBAgrees db before →
      applyLocalPayloads? payloads before = some after →
      db.interrupt = false →
      RuntimeDBAgrees
        (payloads.foldl
          (fun d payload => runtimeApplyPayload pos payload d) db)
        after
  | [], db, before, after, agreement, happly, hint => by
      cases Option.some.inj happly
      exact agreement
  | payload :: rest, db, before, after, agreement, happly, hint => by
      rw [show applyLocalPayloads? (payload :: rest) before =
        (do
          let mid ← applyLocalPayload? payload before
          applyLocalPayloads? rest mid) from rfl] at happly
      obtain ⟨mid, hmid, hrest⟩ := bind_some_inv happly
      rw [List.foldl_cons]
      exact RuntimeDBAgrees.applyPayloads pos
        (RuntimeDBAgrees.applyPayload agreement hmid hint pos)
        hrest
        (by rw [runtimeApplyPayload_interrupt]; exact hint)

/-- From the default runtime database and the
initial source state, any accepted payload sequence co-evolves. -/
theorem default_initial_applyPayloads {payloads : List LocalPayload}
    {after : SourceState} (pos : Pos)
    (happly : applyLocalPayloads? payloads initialState =
      some after) :
    RuntimeDBAgrees
      (payloads.foldl
        (fun d payload => runtimeApplyPayload pos payload d)
        (default : RuntimeDB))
      after :=
  RuntimeDBAgrees.applyPayloads pos
    default_initial_runtimeDBAgrees happly rfl

/-! ### Kernel fixtures for the new joints -/

/-- Fixture payload sequence: constants, a variable, its float,
and an axiom using them. -/
def fixturePayloads : List LocalPayload :=
  [.declareConstants ["wff", "|-"],
   .declareVariables ["x"],
   .declareFloating "vx" "wff" "x",
   .declareAxiom "ax" ⟨"|-", [.var "x"]⟩]

/-- Positive: the sequence is accepted and the shipped runtime fold
co-evolves from the ground states. -/
example : ∃ after,
    applyLocalPayloads? fixturePayloads initialState = some after ∧
    RuntimeDBAgrees
      (fixturePayloads.foldl
        (fun d payload => runtimeApplyPayload ⟨0, 0⟩ payload d)
        (default : RuntimeDB))
      after := by
  have hsome : (applyLocalPayloads? fixturePayloads
      initialState).isSome = true := by decide
  obtain ⟨after, hafter⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨after, hafter, default_initial_applyPayloads _ hafter⟩

/-- Negative: duplicate constants are rejected at the source gate. -/
example : applyLocalPayloads?
    [.declareConstants ["wff", "wff"]] initialState = none := by
  decide

/-- Negative: a name cannot be both constant and variable. -/
example : applyLocalPayloads?
    [.declareConstants ["c"], .declareVariables ["c"]]
    initialState = none := by
  decide

/-- Negative: an axiom whose variable has no floating hypothesis is
rejected. -/
example : applyLocalPayloads?
    [.declareConstants ["wff", "|-"],
     .declareVariables ["x"],
     .declareAxiom "ax" ⟨"|-", [.var "x"]⟩]
    initialState = none := by
  decide

/-- Negative: a runtime database that inserted a symbol the source
never declared cannot agree with the initial state. -/
example :
    ¬ RuntimeDBAgrees
      (insertObj (default : RuntimeDB) "c" (.const "c"))
      initialState := by
  intro h
  have hocc := (h.objectNamespace.occupied_iff "c").mp (by
    rw [find?_insertObj_self]
    simp)
  simp [initialState, SourceState.objectNames] at hocc

end FoldLane

end Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution
