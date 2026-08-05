import Mettapedia.Languages.Metamath.SourceGSLTSpecGrounding
import Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport

/-!
# Dummy allocation: the extended-frame reconciliation crown

[MM §4.2.7] promises that proofs may use "temporary or dummy variables"
through optional hypotheses of an extended frame.  This module cashes the
promise: every canonical declarative derivation
(`Metamath.Provable`, whose `var` rule is unrestricted) becomes a
frame-supported derivation (`SupportedProvable`) over the active frame
extended with finitely many freshly named optional floating hypotheses —
provided only that the conclusion itself lives over the base frame.

This is a theorem about the semantic `Frame` carrier and characterizes the
finite-extension closure of the unrestricted relation.  It does **not** say
that the manufactured names were already declared by a fixed source prefix:
an accepted source transition additionally needs declared `$c` typecodes,
declared `$v` names, and globally fresh `$f` labels.  Fixed-source parser and
checker adequacy therefore remains anchored on `SupportedProvable`; the later
raw-source composition must supply those source-state facts rather than infer
them from frame-local freshness.

The construction composes three sealed pieces:

* `Provable.exists_finiteSupport` — a derivation needs only finitely many
  variable leaves (`InferenceSemanticFiniteSupport`);
* `OptionalFloatSequence` / `extendFloats` — ordered optional extension
  with per-step freshness (`SourceGSLTSpecGrounding`);
* a concrete allocation: one fresh dummy per support leaf, with fresh
  names manufactured by a length argument (every string strictly longer
  than every used string is unused, and lengths keep the dummies distinct
  from one another), and the renaming `ρ` that fixes every
  frame-declared variable and sends each ghost to its dummy.

`ρ` fixes everything the base context can mention — hypothesis formulas
and `$d` pairs only contain frame-declared variables — so context
transport is by identity, and the conclusion is returned *unrenamed*.

Positive calibration: `semanticProvable_toSupported_extended` applied to
the support boundary's counterexample.
Negative calibration: the boundary theorem
`not_supportedProvable_target` shows the extension is genuinely needed.
-/

namespace Mettapedia.Languages.Metamath.InferenceDummyAllocation

open Metamath.Spec.Equivalence
open Metamath.Spec.Bridge (MarioVR MarioFormula MarioExpr)
open Mettapedia.Languages.Metamath.SourceGSLTSpecGrounding
open Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport

/-! ## Generic `find?` and membership helpers (self-contained) -/

theorem find?_none_of_all {α : Type _} {p : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = false) → l.find? p = none
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.find?]
      rw [h a (List.Mem.head _)]
      exact find?_none_of_all fun b hb => h b (List.Mem.tail _ hb)

/-- Any pair stored in a variable map can be recovered through `findVar`. -/
theorem findVar_isSome_of_pair_mem {vm : VarMap}
    {entry : Metamath.Spec.Variable × MarioVR} (hmem : entry ∈ vm) :
    ∃ w, findVar vm entry.2 = some w := by
  induction vm with
  | nil => exact nomatch hmem
  | cons head tail ih =>
      by_cases hhead : head.2 = entry.2
      · refine ⟨head.1, ?_⟩
        unfold findVar
        simp [List.find?, hhead]
      · rcases List.mem_cons.mp hmem with rfl | htail
        · exact absurd rfl hhead
        · obtain ⟨w, hw⟩ := ih htail
          refine ⟨w, ?_⟩
          unfold findVar at hw ⊢
          simp only [List.find?]
          have hdec : (decide (head.2 = entry.2)) = false :=
            decide_eq_false hhead
          rw [hdec]
          exact hw

/-- A successful `findVR` result denotes a stored pair. -/
theorem entry_of_findVR_some {vm : VarMap} {x : Metamath.Spec.Variable}
    {a : MarioVR} (h : findVR vm x = some a) :
    ∃ entry ∈ vm, entry.2 = a := by
  unfold findVR at h
  cases hfind : vm.find? (fun p => p.1 = x) with
  | none => rw [hfind] at h; exact nomatch h
  | some q =>
      rw [hfind] at h
      refine ⟨q, List.mem_of_find?_eq_some hfind, Option.some.inj h⟩

/-- Variables reachable through `findVR` are reachable through `findVar`. -/
theorem findVar_isSome_of_findVR_some {vm : VarMap}
    {x : Metamath.Spec.Variable} {a : MarioVR}
    (h : findVR vm x = some a) :
    ∃ w, findVar vm a = some w := by
  obtain ⟨entry, hmem, hsnd⟩ := entry_of_findVR_some h
  subst hsnd
  exact findVar_isSome_of_pair_mem hmem

/-! ## Every variable the base context mentions is frame-declared -/

/-- Variables of a converted expression are images of the variable map. -/
theorem declared_of_mem_exprToMarioExpr {vm : VarMap}
    {e : Metamath.Spec.Expr} {vr : MarioVR}
    (hmem : Metamath.Sym.var vr ∈ exprToMarioExpr vm e) :
    ∃ w, findVar vm vr = some w := by
  unfold exprToMarioExpr at hmem
  rcases List.mem_map.mp hmem with ⟨s, hs, himg⟩
  simp only [toMarioSym] at himg
  cases hfind : findVR vm ⟨s⟩ with
  | none => rw [hfind] at himg; exact nomatch himg
  | some a =>
      rw [hfind] at himg
      have : a = vr := by
        have := Metamath.Sym.var.inj himg
        exact this
      subst this
      exact findVar_isSome_of_findVR_some hfind

/-- Every variable occurring in a base-context hypothesis is declared in
the base frame's variable map. -/
theorem hyp_vars_declared {fr : Metamath.Spec.Frame}
    {formula : MarioFormula}
    (hmem : formula ∈ (frameToContext fr).hyps)
    {vr : MarioVR} (hvr : Metamath.Sym.var vr ∈ formula.2) :
    ∃ w, findVar (varMapOfFrame fr) vr = some w := by
  rw [frameToContext_hyps] at hmem
  rcases List.mem_map.mp hmem with ⟨h₀, hh₀, himg⟩
  cases h₀ with
  | floating c w =>
      have hw : w ∈ fr.vars := by
        unfold Metamath.Spec.Frame.vars
        exact List.mem_filterMap.mpr ⟨_, hh₀, rfl⟩
      obtain ⟨c', hc'⟩ := exists_float_of_mem_vars hw
      obtain ⟨vrW, hvrW⟩ := findVR_isSome_of_mem_aux ⟨c', hc'⟩ 0
      have hvrW' : findVR (varMapOfFrame fr) w = some vrW := hvrW
      have hform : formula = (c.c, [Metamath.Sym.var vrW]) := by
        rw [← himg]
        simp only [hypToMarioFormula]
        rw [hvrW']
        rfl
      rw [hform] at hvr
      have : vr = vrW := by
        rcases List.mem_singleton.mp hvr with heq
        exact (Metamath.Sym.var.inj heq)
      subst this
      exact findVar_isSome_of_findVR_some hvrW'
  | essential e =>
      have hform : formula =
          exprToFormula (varMapOfFrame fr) e := by
        rw [← himg]
        rfl
      have : Metamath.Sym.var vr ∈
          exprToMarioExpr (varMapOfFrame fr) e := by
        have h2 := congrArg Prod.snd hform
        rw [h2] at hvr
        exact hvr
      exact declared_of_mem_exprToMarioExpr this

/-- Both members of every base-context `$d` pair are frame-declared. -/
theorem dj_vars_declared {fr : Metamath.Spec.Frame} {a b : MarioVR}
    (hab : (frameToContext fr).dj a b) :
    (∃ w, findVar (varMapOfFrame fr) a = some w) ∧
      (∃ w, findVar (varMapOfFrame fr) b = some w) := by
  obtain ⟨-, hor⟩ := hab
  have handle : ∀ {x y : MarioVR},
      (x, y) ∈ (fr.dv.filterMap fun p =>
        match findVR (varMapOfFrame fr) p.1,
              findVR (varMapOfFrame fr) p.2 with
        | some a, some b => some (a, b)
        | _, _ => none) →
      (∃ w, findVar (varMapOfFrame fr) x = some w) ∧
        (∃ w, findVar (varMapOfFrame fr) y = some w) := by
    intro x y hxy
    rcases List.mem_filterMap.mp hxy with ⟨p, hp, hmatch⟩
    cases h1 : findVR (varMapOfFrame fr) p.1 with
    | none => rw [h1] at hmatch; exact nomatch hmatch
    | some a' =>
        cases h2 : findVR (varMapOfFrame fr) p.2 with
        | none => rw [h1, h2] at hmatch; exact nomatch hmatch
        | some b' =>
            rw [h1, h2] at hmatch
            have hxa : a' = x := congrArg Prod.fst (Option.some.inj hmatch)
            have hyb : b' = y := congrArg Prod.snd (Option.some.inj hmatch)
            subst hxa; subst hyb
            exact ⟨findVar_isSome_of_findVR_some h1,
              findVar_isSome_of_findVR_some h2⟩
  rcases hor with hp | hp
  · exact handle hp
  · exact ⟨(handle hp).2, (handle hp).1⟩

/-! ## The ghost renaming -/

variable (fr : Metamath.Spec.Frame)

/-- Position of the first occurrence in a list (own definition, so its
equations are exactly what the proofs use). -/
def posOf : List MarioVR → MarioVR → Nat
  | [], _ => 0
  | a :: l, v => if a = v then 0 else posOf l v + 1

/-- The ghost renaming: frame-declared variables are fixed; every other
variable is sent to the dummy slot reserved for its first occurrence in
the support list, preserving its typecode. -/
def ghostRename (support : List MarioVR) (base : Nat) :
    MarioVR → MarioVR :=
  fun v =>
    if (findVar (varMapOfFrame fr) v).isSome then v
    else ⟨v.type, base + posOf support v⟩

theorem ghostRename_typePreserving (support : List MarioVR) (base : Nat) :
    TypePreserving (ghostRename fr support base) := by
  intro v
  unfold ghostRename
  by_cases h : (findVar (varMapOfFrame fr) v).isSome
  · rw [if_pos h]
  · rw [if_neg h]

theorem ghostRename_declared {support : List MarioVR} {base : Nat}
    {v : MarioVR} {w : Metamath.Spec.Variable}
    (h : findVar (varMapOfFrame fr) v = some w) :
    ghostRename fr support base v = v := by
  unfold ghostRename
  rw [if_pos (by rw [h]; rfl)]

theorem ghostRename_ghost {support : List MarioVR} {base : Nat}
    {v : MarioVR} (h : findVar (varMapOfFrame fr) v = none) :
    ghostRename fr support base v = ⟨v.type, base + posOf support v⟩ := by
  simp [ghostRename, h]

/-- Renaming is the identity on any expression whose variables are all
frame-declared. -/
theorem renameExpr_id_of_declared {support : List MarioVR} {base : Nat} :
    ∀ {e : MarioExpr},
      (∀ vr, Metamath.Sym.var vr ∈ e →
        ∃ w, findVar (varMapOfFrame fr) vr = some w) →
      renameExpr (ghostRename fr support base) e = e
  | [], _ => rfl
  | .const c :: tail, h => by
      rw [renameExpr_const_cons,
        renameExpr_id_of_declared fun vr hvr =>
          h vr (List.Mem.tail _ hvr)]
  | .var v :: tail, h => by
      rw [renameExpr_var_cons,
        renameExpr_id_of_declared fun vr hvr =>
          h vr (List.Mem.tail _ hvr)]
      obtain ⟨w, hw⟩ := h v (List.Mem.head _)
      rw [ghostRename_declared fr hw]

/-! ## Fresh-name manufacture by length -/

/-- All variable and essential-hypothesis strings a frame can obstruct
freshness with. -/
def usedStrings (fr : Metamath.Spec.Frame) : List String :=
  fr.vars.map (·.v) ++
    fr.hyps.flatMap fun h =>
      match h with
      | .essential e => e.syms
      | .floating _ _ => []

/-- Fold-maximum of string lengths. -/
def maxLength (l : List String) : Nat :=
  l.foldr (fun s acc => max s.length acc) 0

theorem length_le_maxLength : ∀ {l : List String} {s : String},
    s ∈ l → s.length ≤ maxLength l
  | _ :: tail, s, h => by
      rcases List.mem_cons.mp h with rfl | htail
      · exact le_max_left _ _
      · exact le_trans (length_le_maxLength htail) (le_max_right _ _)

/-- The dummy name of slot `i`: strictly longer than every used string,
and pairwise distinct across slots by length. -/
def dummyName (bound i : Nat) : String :=
  String.ofList (List.replicate (bound + 1 + i) 'd')

theorem dummyName_length (bound i : Nat) :
    (dummyName bound i).length = bound + 1 + i := by
  simp [dummyName]

theorem dummyName_injOn_length {bound i j : Nat}
    (h : dummyName bound i = dummyName bound j) : i = j := by
  have := congrArg String.length h
  rw [dummyName_length, dummyName_length] at this
  omega

theorem dummyName_not_used {l : List String} {bound i : Nat}
    (hbound : maxLength l ≤ bound) :
    dummyName bound i ∉ l := by
  intro hmem
  have h1 := length_le_maxLength hmem
  have h2 := dummyName_length bound i
  omega

/-! ## The allocation -/

/-- One optional floating declaration per support slot: the typecode is
the leaf's semantic typecode, the variable name is the slot's dummy. -/
def allocate (bound : Nat) : List MarioVR → Nat →
    List (Metamath.Spec.Constant × Metamath.Spec.Variable)
  | [], _ => []
  | v :: rest, i => (⟨v.type⟩, ⟨dummyName bound i⟩) :: allocate bound rest (i + 1)

theorem allocate_length (bound : Nat) :
    ∀ (support : List MarioVR) (i : Nat),
      (allocate bound support i).length = support.length
  | [], _ => rfl
  | _ :: rest, i => by
      simp [allocate, allocate_length bound rest (i + 1)]

/-- Every variable name the allocation introduces is a dummy of slot
`≥ i`. -/
theorem allocate_names (bound : Nat) :
    ∀ {support : List MarioVR} {i : Nat} {c : Metamath.Spec.Constant}
      {v : Metamath.Spec.Variable},
      (c, v) ∈ allocate bound support i →
      ∃ j, i ≤ j ∧ v = ⟨dummyName bound j⟩
  | v₀ :: rest, i, c, v, h => by
      rcases List.mem_cons.mp h with heq | htail
      · exact ⟨i, le_refl _, congrArg Prod.snd heq⟩
      · obtain ⟨j, hij, hv⟩ := allocate_names bound htail
        exact ⟨j, Nat.le_of_succ_le hij, hv⟩

/-! ## Freshness of the allocation sequence -/

/-- The essential hypotheses of an extended frame are those of the base
frame. -/
theorem essential_mem_extendFloat {fr : Metamath.Spec.Frame}
    {c : Metamath.Spec.Constant} {v : Metamath.Spec.Variable}
    {e : Metamath.Spec.Expr}
    (h : Metamath.Spec.Hyp.essential e ∈ (extendFloat fr c v).hyps) :
    Metamath.Spec.Hyp.essential e ∈ fr.hyps := by
  unfold extendFloat at h
  rcases List.mem_append.mp h with hleft | hright
  · exact hleft
  · rcases List.mem_singleton.mp hright with heq
    exact nomatch heq

/-- Bounded-name invariant: every string a frame can obstruct with is
strictly shorter than the next dummy. -/
def NamesBounded (fr : Metamath.Spec.Frame) (bound i : Nat) : Prop :=
  ∀ s ∈ usedStrings fr, s.length < bound + 1 + i

theorem namesBounded_extendFloat {fr : Metamath.Spec.Frame}
    {bound i : Nat} (h : NamesBounded fr bound i)
    (c : Metamath.Spec.Constant) :
    NamesBounded (extendFloat fr c ⟨dummyName bound i⟩) bound (i + 1) := by
  intro s hs
  unfold usedStrings at hs
  rcases List.mem_append.mp hs with hvars | hess
  · rcases List.mem_map.mp hvars with ⟨w, hw, rfl⟩
    rw [frameVars_extendFloat] at hw
    rcases List.mem_append.mp hw with hbase | hnew
    · have : w.v ∈ usedStrings fr := by
        unfold usedStrings
        exact List.mem_append_left _ (List.mem_map.mpr ⟨w, hbase, rfl⟩)
      have := h _ this
      omega
    · rcases List.mem_singleton.mp hnew with rfl
      show (dummyName bound i).length < bound + 1 + (i + 1)
      rw [dummyName_length]
      omega
  · rcases List.mem_flatMap.mp hess with ⟨hyp, hhyp, hsym⟩
    cases hyp with
    | floating _ _ => exact nomatch hsym
    | essential e =>
        have hbase := essential_mem_extendFloat hhyp
        have : s ∈ usedStrings fr := by
          unfold usedStrings
          refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hbase, hsym⟩)
        have := h _ this
        omega

theorem optionalFresh_of_bounded {fr : Metamath.Spec.Frame}
    {bound i : Nat} (h : NamesBounded fr bound i) :
    OptionalFresh fr ⟨dummyName bound i⟩ := by
  constructor
  · intro hmem
    have : (Metamath.Spec.Variable.mk (dummyName bound i)).v ∈
        usedStrings fr := by
      unfold usedStrings
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
    have hlt := h _ this
    have hlen := dummyName_length bound i
    simp only [] at hlt
    omega
  · intro e hmem hsym
    have : dummyName bound i ∈ usedStrings fr := by
      unfold usedStrings
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hmem, hsym⟩)
    have hlt := h _ this
    have hlen := dummyName_length bound i
    omega

/-- The allocation is a valid optional-float sequence from any frame whose
used strings respect the bound. -/
theorem allocate_sequence (bound : Nat) :
    ∀ (support : List MarioVR) (fr : Metamath.Spec.Frame) (i : Nat),
      NamesBounded fr bound i →
      OptionalFloatSequence fr (allocate bound support i)
  | [], fr, i, _ => .nil fr
  | v :: rest, fr, i, h => by
      refine .cons (optionalFresh_of_bounded h) ?_
      exact allocate_sequence bound rest _ (i + 1)
        (namesBounded_extendFloat h ⟨v.type⟩)

/-! ## Locating dummies in the extended variable map -/

/-- Index window of an auxiliary variable map segment. -/
theorem varMapOfFrameAux_index_bound :
    ∀ {l : List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
      {n : Nat} {entry : Metamath.Spec.Variable × MarioVR},
      entry ∈ varMapOfFrameAux n l →
      n ≤ entry.2.i ∧ entry.2.i < n + l.length
  | (c, v) :: rest, n, entry, h => by
      rcases List.mem_cons.mp h with rfl | htail
      · simp
      · obtain ⟨h1, h2⟩ := varMapOfFrameAux_index_bound htail
        constructor
        · omega
        · simp only [List.length_cons]
          omega

/-- The dummy VR of the first occurrence of a support leaf is found at its
allocated slot. -/
theorem findVar_allocate (bound : Nat) :
    ∀ (support : List MarioVR) (v : MarioVR), v ∈ support → ∀ (n i : Nat),
      findVar (varMapOfFrameAux n (allocate bound support i))
        ⟨v.type, n + posOf support v⟩ =
        some ⟨dummyName bound (i + posOf support v)⟩
  | v₀ :: rest, v, hv, n, i => by
      by_cases hhead : v₀ = v
      · subst hhead
        unfold posOf
        rw [if_pos rfl]
        unfold findVar allocate varMapOfFrameAux
        simp [List.find?]
      · unfold posOf
        rw [if_neg hhead]
        have hvtail : v ∈ rest := by
          rcases List.mem_cons.mp hv with rfl | htail
          · exact absurd rfl hhead
          · exact htail
        have ih := findVar_allocate bound rest v hvtail (n + 1) (i + 1)
        unfold findVar at ih ⊢
        unfold allocate varMapOfFrameAux
        simp only [List.find?]
        have hne : (decide ((⟨v₀.type, n⟩ : MarioVR) =
            ⟨v.type, n + (posOf rest v + 1)⟩)) = false := by
          refine decide_eq_false fun heq => ?_
          have := congrArg Metamath.VR.i heq
          simp at this
        rw [hne]
        have harith1 : n + (posOf rest v + 1) = (n + 1) + posOf rest v := by
          omega
        have harith2 : i + (posOf rest v + 1) = (i + 1) + posOf rest v := by
          omega
        rw [harith1, harith2]
        exact ih

/-- Base-context hypotheses survive a whole optional batch extension. -/
theorem frameToContext_hyps_extendFloats
    {fr : Metamath.Spec.Frame}
    {declarations :
      List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
    (hseq : OptionalFloatSequence fr declarations)
    {g : MarioFormula} (hg : g ∈ (frameToContext fr).hyps) :
    g ∈ (frameToContext (extendFloats fr declarations)).hyps := by
  induction hseq with
  | nil => exact hg
  | @cons fr c v rest hfresh htail ih =>
      exact ih (frameToContext_hyps_extendFloat hfresh hg)

/-- Base-context disjointness survives a whole optional batch extension. -/
theorem frameToContext_dj_le_extendFloats
    {fr : Metamath.Spec.Frame}
    {declarations :
      List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
    (hseq : OptionalFloatSequence fr declarations) :
    (frameToContext fr).dj ≤
      (frameToContext (extendFloats fr declarations)).dj := by
  induction hseq with
  | nil => exact Metamath.DJ.refl _
  | @cons fr c v rest hfresh htail ih =>
      intro a b hab
      exact ih a b (frameToContext_dj_le fr c v a b hab)

/-! ## The crown -/

/-- **[MM §4.2.7] Semantic extended-frame reconciliation.**  Every declarative
derivation over a base active frame becomes a frame-supported derivation
after adjoining finitely many freshly named optional floating hypotheses,
whenever the conclusion mentions only base-frame variables.  The optional
frame declarations are constructed, not assumed: one typed dummy per finite
support leaf, with frame-local freshness certified per step.  This theorem
does not manufacture the separate `$c`, `$v`, and labelled `$f` source
operations required to realize that semantic extension in a fixed source
prefix. -/
theorem semanticProvable_toSupported_extended
    {Γ : Metamath.Spec.Database} {fr : Metamath.Spec.Frame}
    {formula : MarioFormula}
    (hconcl : ∀ vr, Metamath.Sym.var vr ∈ formula.2 →
      ∃ w, findVar (varMapOfFrame fr) vr = some w)
    (h : Metamath.Provable (dbToAxioms Γ) (frameToContext fr) formula) :
    ∃ declarations,
      OptionalFloatSequence fr declarations ∧
      SupportedProvable Γ (extendFloats fr declarations) formula := by
  classical
  obtain ⟨support, hwitness⟩ := Provable.exists_finiteSupport h
  set bound := maxLength (usedStrings fr) with hbound
  set base := (floatList fr).length with hbase
  set declarations := allocate bound support 0 with hdecls
  set ρ := ghostRename fr support base with hρ
  have hseq : OptionalFloatSequence fr declarations :=
    allocate_sequence bound support fr 0
      (fun s hs => by
        have := length_le_maxLength hs
        omega)
  set target := extendFloats fr declarations with htarget
  have hvm : varMapOfFrame target =
      varMapOfFrame fr ++ varMapOfFrameAux base declarations := by
    rw [htarget, varMapOfFrame_extendFloats]
  -- Every base-declared variable keeps its lookup in the target.
  have hstable : ∀ {v : MarioVR} {w : Metamath.Spec.Variable},
      findVar (varMapOfFrame fr) v = some w →
      findVar (varMapOfFrame target) v = some w := by
    intro v w hv
    rw [hvm]
    exact findVar_append_of_some hv
  -- Context transport: ρ is the identity on everything the context mentions.
  have hyps_stable : ∀ {g : MarioFormula},
      g ∈ (frameToContext fr).hyps →
      g ∈ (frameToContext target).hyps :=
    fun hg => frameToContext_hyps_extendFloats hseq hg
  have dj_stable : ∀ {a b : MarioVR},
      (frameToContext fr).dj a b →
      (frameToContext target).dj a b :=
    fun hab => frameToContext_dj_le_extendFloats hseq _ _ hab
  have hcontext : ContextTransport ρ (frameToContext fr) target := by
    constructor
    · intro formula₀ hmem
      have hid : renameFormula ρ formula₀ = formula₀ := by
        unfold renameFormula
        have := renameExpr_id_of_declared fr
          (support := support) (base := base)
          (e := formula₀.2)
          (fun vr hvr => hyp_vars_declared hmem hvr)
        rw [this]
        rfl
      rw [hid]
      exact hyps_stable hmem
    · intro a b hab
      obtain ⟨⟨wa, hwa⟩, ⟨wb, hwb⟩⟩ := dj_vars_declared hab
      rw [hρ, ghostRename_declared fr hwa, ghostRename_declared fr hwb]
      exact dj_stable hab
  -- All support images are findable in the target.
  have hsupported : ∀ v ∈ support,
      ∃ w, findVar (varMapOfFrame target) (ρ v) = some w := by
    intro v hv
    cases hfind : findVar (varMapOfFrame fr) v with
    | some w =>
        rw [hρ, ghostRename_declared fr hfind]
        exact ⟨w, hstable hfind⟩
    | none =>
        rw [hρ, ghostRename_ghost fr hfind]
        refine ⟨⟨dummyName bound (0 + posOf support v)⟩, ?_⟩
        rw [hvm]
        have hprefix : (varMapOfFrame fr).find?
            (fun p => p.2 =
              (⟨v.type, base + posOf support v⟩ : MarioVR)) = none := by
          refine find?_none_of_all fun entry hentry => ?_
          refine decide_eq_false fun heq => ?_
          have hb := varMapOfFrameAux_index_bound
            (l := floatList fr) (n := 0) (entry := entry)
            (show entry ∈ varMapOfFrameAux 0 (floatList fr) from hentry)
          have hidx := congrArg Metamath.VR.i heq
          simp only [] at hidx
          omega
        have halloc := findVar_allocate bound support v hv base 0
        unfold findVar at halloc ⊢
        rw [find?_append_of_none hprefix]
        exact halloc
  have htype : TypePreserving ρ := ghostRename_typePreserving fr support base
  have hmain := hwitness ρ target htype hcontext hsupported
  have hid : renameFormula ρ formula = formula := by
    unfold renameFormula
    rw [renameExpr_id_of_declared fr
      (support := support) (base := base) (e := formula.2) hconcl]
    rfl
  rw [hid] at hmain
  exact ⟨declarations, hseq, hmain⟩

/-! ## Calibration against the support boundary -/

open Mettapedia.Languages.Metamath.InferenceSupportedProvableBoundary in
/-- Positive: the boundary counterexample's unrestricted derivation of
`|- c` over the empty frame transports into some finite optional
extension — the constructive general form of the hand-built repair
witness. -/
example :
    ∃ declarations,
      OptionalFloatSequence
        InferenceSupportedProvableBoundary.emptyFrame declarations ∧
      SupportedProvable counterexampleDatabase
        (extendFloats InferenceSupportedProvableBoundary.emptyFrame
          declarations)
        InferenceSupportedProvableBoundary.target := by
  refine semanticProvable_toSupported_extended ?_ semantic_provable_target
  intro vr hvr
  have heq := List.mem_singleton.mp hvr
  exact Metamath.Sym.noConfusion heq

/-! ## Positionally typed plans: the name-free generalization

`findVar_allocate`'s hit/miss argument never inspects the manufactured
names — only positional indices and per-slot typecodes.  `TypedAlong`
captures exactly that interface, so the crown's assembly applies to any
declaration list whose typecodes align positionally with the support —
in particular to source-accepted supply plans whose names are
manufactured by the source-state layer rather than by `dummyName`. -/

/-- The declarations follow the support positionally: same length, and
each slot's typecode is the corresponding support leaf's semantic
typecode.  Names are unconstrained. -/
inductive TypedAlong :
    List MarioVR →
      List (Metamath.Spec.Constant × Metamath.Spec.Variable) → Prop
  | nil : TypedAlong [] []
  | cons {v : MarioVR} {c : Metamath.Spec.Constant}
      {x : Metamath.Spec.Variable} {support : List MarioVR}
      {decls : List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
      (htype : c.c = v.type)
      (htail : TypedAlong support decls) :
      TypedAlong (v :: support) ((c, x) :: decls)

/-- The manufactured allocation is positionally typed (the special
case). -/
theorem allocate_typedAlong (bound : Nat) :
    ∀ (support : List MarioVR) (i : Nat),
      TypedAlong support (allocate bound support i)
  | [], _ => .nil
  | _ :: rest, i => .cons rfl (allocate_typedAlong bound rest (i + 1))

/-- Positional lookup: the first occurrence of a support leaf is found at
its slot in **any** positionally typed declaration list — names are
irrelevant to the variable-map lookup. -/
theorem findVar_typedAlong {support : List MarioVR}
    {decls : List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
    (htyped : TypedAlong support decls) :
    ∀ {v : MarioVR}, v ∈ support → ∀ (n : Nat),
      ∃ w, findVar (varMapOfFrameAux n decls)
        ⟨v.type, n + posOf support v⟩ = some w := by
  induction htyped with
  | nil =>
      intro _ hv _
      exact nomatch hv
  | @cons v₀ c x support decls htype htail ih =>
      intro v hv n
      by_cases hhead : v₀ = v
      · subst hhead
        refine ⟨x, ?_⟩
        unfold posOf
        rw [if_pos rfl]
        unfold findVar varMapOfFrameAux
        simp [List.find?, htype]
      · unfold posOf
        rw [if_neg hhead]
        have hvtail : v ∈ support := by
          rcases List.mem_cons.mp hv with rfl | htl
          · exact absurd rfl hhead
          · exact htl
        obtain ⟨w, hw⟩ := ih hvtail (n + 1)
        refine ⟨w, ?_⟩
        unfold findVar at hw ⊢
        unfold varMapOfFrameAux
        simp only [List.find?]
        have hne : (decide ((⟨c.c, n⟩ : MarioVR) =
            ⟨v.type, n + (posOf support v + 1)⟩)) = false := by
          refine decide_eq_false fun heq => ?_
          have := congrArg Metamath.VR.i heq
          simp at this
        rw [hne]
        have harith : n + (posOf support v + 1) =
            (n + 1) + posOf support v := by
          omega
        rw [harith]
        exact hw

/-- **Name-free crown generalization.**  A finite-support witness over a
base frame yields a supported derivation over the frame extended by
**any** optional-float sequence positionally typed along the support.
The renaming and transport assembly is exactly the crown's; only the
lookup of ghost images changes, through `findVar_typedAlong`. -/
theorem witness_toSupported_typedPlan
    {Γ : Metamath.Spec.Database} {fr : Metamath.Spec.Frame}
    {formula : MarioFormula} {support : List MarioVR}
    (hwitness : FiniteSupportWitness (Γ := Γ)
      (source := frameToContext fr) (formula := formula) support)
    (hconcl : ∀ vr, Metamath.Sym.var vr ∈ formula.2 →
      ∃ w, findVar (varMapOfFrame fr) vr = some w)
    {decls : List (Metamath.Spec.Constant × Metamath.Spec.Variable)}
    (htyped : TypedAlong support decls)
    (hseq : OptionalFloatSequence fr decls) :
    SupportedProvable Γ (extendFloats fr decls) formula := by
  classical
  set base := (floatList fr).length with hbase
  set ρ := ghostRename fr support base with hρ
  set target := extendFloats fr decls with htarget
  have hvm : varMapOfFrame target =
      varMapOfFrame fr ++ varMapOfFrameAux base decls := by
    rw [htarget, varMapOfFrame_extendFloats]
  have hstable : ∀ {v : MarioVR} {w : Metamath.Spec.Variable},
      findVar (varMapOfFrame fr) v = some w →
      findVar (varMapOfFrame target) v = some w := by
    intro v w hv
    rw [hvm]
    exact findVar_append_of_some hv
  have hyps_stable : ∀ {g : MarioFormula},
      g ∈ (frameToContext fr).hyps →
      g ∈ (frameToContext target).hyps :=
    fun hg => frameToContext_hyps_extendFloats hseq hg
  have dj_stable : ∀ {a b : MarioVR},
      (frameToContext fr).dj a b →
      (frameToContext target).dj a b :=
    fun hab => frameToContext_dj_le_extendFloats hseq _ _ hab
  have hcontext : ContextTransport ρ (frameToContext fr) target := by
    constructor
    · intro formula₀ hmem
      have hid : renameFormula ρ formula₀ = formula₀ := by
        unfold renameFormula
        have := renameExpr_id_of_declared fr
          (support := support) (base := base)
          (e := formula₀.2)
          (fun vr hvr => hyp_vars_declared hmem hvr)
        rw [this]
        rfl
      rw [hid]
      exact hyps_stable hmem
    · intro a b hab
      obtain ⟨⟨wa, hwa⟩, ⟨wb, hwb⟩⟩ := dj_vars_declared hab
      rw [hρ, ghostRename_declared fr hwa, ghostRename_declared fr hwb]
      exact dj_stable hab
  have hsupported : ∀ v ∈ support,
      ∃ w, findVar (varMapOfFrame target) (ρ v) = some w := by
    intro v hv
    cases hfind : findVar (varMapOfFrame fr) v with
    | some w =>
        rw [hρ, ghostRename_declared fr hfind]
        exact ⟨w, hstable hfind⟩
    | none =>
        rw [hρ, ghostRename_ghost fr hfind]
        obtain ⟨w, hw⟩ := findVar_typedAlong htyped hv base
        refine ⟨w, ?_⟩
        rw [hvm]
        have hprefix : (varMapOfFrame fr).find?
            (fun p => p.2 =
              (⟨v.type, base + posOf support v⟩ : MarioVR)) = none := by
          refine find?_none_of_all fun entry hentry => ?_
          refine decide_eq_false fun heq => ?_
          have hb := varMapOfFrameAux_index_bound
            (l := floatList fr) (n := 0) (entry := entry)
            (show entry ∈ varMapOfFrameAux 0 (floatList fr) from hentry)
          have hidx := congrArg Metamath.VR.i heq
          simp only [] at hidx
          omega
        unfold findVar at hw ⊢
        rw [find?_append_of_none hprefix]
        exact hw
  have htype : TypePreserving ρ := ghostRename_typePreserving fr support base
  have hmain := hwitness ρ target htype hcontext hsupported
  have hid : renameFormula ρ formula = formula := by
    unfold renameFormula
    rw [renameExpr_id_of_declared fr
      (support := support) (base := base) (e := formula.2) hconcl]
    rfl
  rw [hid] at hmain
  exact hmain

/-- Coherence: the sealed crown's statement is recovered from the
name-free generalization at the `allocate` plan — the generalization is
genuinely stronger, not a restatement. -/
example {Γ : Metamath.Spec.Database} {fr : Metamath.Spec.Frame}
    {formula : MarioFormula}
    (hconcl : ∀ vr, Metamath.Sym.var vr ∈ formula.2 →
      ∃ w, findVar (varMapOfFrame fr) vr = some w)
    (h : Metamath.Provable (dbToAxioms Γ) (frameToContext fr) formula) :
    ∃ declarations,
      OptionalFloatSequence fr declarations ∧
      SupportedProvable Γ (extendFloats fr declarations) formula := by
  classical
  obtain ⟨support, hwitness⟩ := Provable.exists_finiteSupport h
  set bound := maxLength (usedStrings fr) with hbound
  have hseq : OptionalFloatSequence fr (allocate bound support 0) :=
    allocate_sequence bound support fr 0
      (fun s hs => by
        have := length_le_maxLength hs
        omega)
  exact ⟨allocate bound support 0, hseq,
    witness_toSupported_typedPlan hwitness hconcl
      (allocate_typedAlong bound support 0) hseq⟩

end Mettapedia.Languages.Metamath.InferenceDummyAllocation
