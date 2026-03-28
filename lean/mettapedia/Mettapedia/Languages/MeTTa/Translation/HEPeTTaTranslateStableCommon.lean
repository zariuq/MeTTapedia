import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateCore
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaValidatedSurface

/-!
# Stable-Common Fixed-Point Theorems

Fixed-point, shared-fragment, and first-order `foldall` theorems extracted from
`HEPeTTaTranslate.lean` so they can be checked separately under tighter
resource limits.
-/

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

mutual

private theorem translateHE_id_of_stableCommonForm_aux
    (a : Atom) (s : Nat) (h : isStableCommonForm a = true) :
    translateHE a s = (a, s) := by
  cases a with
  | var _ => rfl
  | symbol _ => rfl
  | grounded _ => rfl
  | expression es =>
    cases es with
    | nil => rfl
    | cons hd args =>
      cases hd with
      | symbol c =>
        by_cases hchain : c = "chain"
        · subst hchain; simp [isStableCommonForm] at h
        · by_cases hcollapse : c = "collapse-bind"
          · subst hcollapse; simp [isStableCommonForm] at h
          · by_cases hsuperpose : c = "superpose-bind"
            · subst hsuperpose; simp [isStableCommonForm] at h
            · by_cases hswitch : c = "switch"
              · subst hswitch; simp [isStableCommonForm] at h
              · by_cases hswitchm : c = "switch-minimal"
                · subst hswitchm; simp [isStableCommonForm] at h
                · by_cases hatomsubst : c = "atom-subst"
                  · subst hatomsubst; simp [isStableCommonForm] at h
                  · by_cases hnop : c = "nop"
                    · subst hnop; simp [isStableCommonForm] at h
                    · by_cases hfunction : c = "function"
                      · subst hfunction; simp [isStableCommonForm] at h
                      · by_cases hfoldall : c = "foldall"
                        · subst hfoldall
                          simp [isStableCommonForm] at h
                        · have hargs : isStableCommonList args = true := by
                            have hprogn : c ≠ "progn" := by
                              intro hc
                              subst hc
                              simp [isStableCommonForm] at h
                            have hprog1 : c ≠ "prog1" := by
                              intro hc
                              subst hc
                              simp [isStableCommonForm] at h
                            have hlt : c ≠ "@<" := by
                              intro hc
                              subst hc
                              simp [isStableCommonForm] at h
                            have hgt : c ≠ "@>" := by
                              intro hc
                              subst hc
                              simp [isStableCommonForm] at h
                            have hparts :
                                isStableCommonHead (.symbol c) = true ∧
                                  isStableCommonList args = true := by
                              simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                                isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose, hswitch,
                                hswitchm, hatomsubst, hnop, hfunction, hfoldall, hprogn,
                                hprog1, hlt, hgt] using h
                            exact hparts.2
                          have htail := translateHEList_id_of_stableCommonList_aux args s hargs
                          have htail₁ : (translateHE.translateHEList args s).1 = args := by
                            exact congrArg Prod.fst htail
                          have htail₂ : (translateHE.translateHEList args s).2 = s := by
                            exact congrArg Prod.snd htail
                          simp [translateHE, translateHE.translateHEList, hchain, hcollapse,
                            hsuperpose, hswitch, hswitchm, hatomsubst, hnop, hfunction,
                            hfoldall, htail₁, htail₂]
      | var v =>
        have hargs : isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have htail := translateHEList_id_of_stableCommonList_aux args s hargs
        simp [translateHE, translateHE.translateHEList, htail]
      | grounded g =>
        have hargs : isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have htail := translateHEList_id_of_stableCommonList_aux args s hargs
        simp [translateHE, translateHE.translateHEList, htail]
      | expression es' =>
        have hparts : isStableCommonForm (.expression es') = true ∧ isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have hhd := translateHE_id_of_stableCommonForm_aux (.expression es') s hparts.1
        have htail := translateHEList_id_of_stableCommonList_aux args s hparts.2
        simp [translateHE, translateHE.translateHEList, hhd, htail]

private theorem translateHEList_id_of_stableCommonList_aux
    (xs : List Atom) (s : Nat) (h : isStableCommonList xs = true) :
    translateHE.translateHEList xs s = (xs, s) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp [isStableCommonList, Bool.and_eq_true] at h
    have hx := translateHE_id_of_stableCommonForm_aux x s h.1
    have hxs := translateHEList_id_of_stableCommonList_aux xs s h.2
    simp [translateHE.translateHEList, hx, hxs]
end

/-- `translateHE` is identity on the stable common fragment. -/
theorem translateHE_id_of_stableCommonForm (a : Atom) (s : Nat)
    (h : isStableCommonForm a = true) :
    translateHE a s = (a, s) := by
  exact translateHE_id_of_stableCommonForm_aux a s h

mutual

private theorem translatePeTTa_id_of_stableCommonForm_aux
    (a : Atom) (s : Nat) (h : isStableCommonForm a = true) :
    translatePeTTa a s = (a, s) := by
  cases a with
  | var _ => rfl
  | symbol _ => rfl
  | grounded _ => rfl
  | expression es =>
    cases es with
    | nil => rfl
    | cons hd args =>
      cases hd with
      | symbol c =>
        by_cases hprogn : c = "progn"
        · subst hprogn; simp [isStableCommonForm] at h
        · by_cases hprog1 : c = "prog1"
          · subst hprog1; simp [isStableCommonForm] at h
          · by_cases hfoldall : c = "foldall"
            · subst hfoldall; simp [isStableCommonForm] at h
            · by_cases hlt : c = "@<"
              · subst hlt; simp [isStableCommonForm] at h
              · by_cases hgt : c = "@>"
                · subst hgt; simp [isStableCommonForm] at h
                · have hchain : c ≠ "chain" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hcollapse : c ≠ "collapse-bind" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hsuperpose : c ≠ "superpose-bind" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hswitch : c ≠ "switch" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hswitchm : c ≠ "switch-minimal" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hatomsubst : c ≠ "atom-subst" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hnop : c ≠ "nop" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hfunction : c ≠ "function" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hparts :
                      isStableCommonHead (.symbol c) = true ∧
                        isStableCommonList args = true := by
                    simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                      isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose, hswitch,
                      hswitchm, hatomsubst, hnop, hfunction, hprogn, hprog1, hfoldall,
                      hlt, hgt] using h
                  have htail := translatePeTTaList_id_of_stableCommonList_aux args s hparts.2
                  have htail₁ : (translatePeTTa.translatePeTTaList args s).1 = args := by
                    exact congrArg Prod.fst htail
                  have htail₂ : (translatePeTTa.translatePeTTaList args s).2 = s := by
                    exact congrArg Prod.snd htail
                  simp [translatePeTTa, translatePeTTa.translatePeTTaList, hprogn, hprog1,
                    hfoldall, hlt, hgt, htail₁, htail₂]
      | var v =>
        have hargs : isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have htail := translatePeTTaList_id_of_stableCommonList_aux args s hargs
        simp [translatePeTTa, translatePeTTa.translatePeTTaList, htail]
      | grounded g =>
        have hargs : isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have htail := translatePeTTaList_id_of_stableCommonList_aux args s hargs
        simp [translatePeTTa, translatePeTTa.translatePeTTaList, htail]
      | expression es' =>
        have hparts : isStableCommonForm (.expression es') = true ∧ isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have hhd := translatePeTTa_id_of_stableCommonForm_aux (.expression es') s hparts.1
        have htail := translatePeTTaList_id_of_stableCommonList_aux args s hparts.2
        simp [translatePeTTa, translatePeTTa.translatePeTTaList, hhd, htail]

private theorem translatePeTTaList_id_of_stableCommonList_aux
    (xs : List Atom) (s : Nat) (h : isStableCommonList xs = true) :
    translatePeTTa.translatePeTTaList xs s = (xs, s) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp [isStableCommonList, Bool.and_eq_true] at h
    have hx := translatePeTTa_id_of_stableCommonForm_aux x s h.1
    have hxs := translatePeTTaList_id_of_stableCommonList_aux xs s h.2
    simp [translatePeTTa.translatePeTTaList, hx, hxs]
end

/-- `translatePeTTa` is identity on the stable common fragment. -/
theorem translatePeTTa_id_of_stableCommonForm (a : Atom) (s : Nat)
    (h : isStableCommonForm a = true) :
    translatePeTTa a s = (a, s) := by
  exact translatePeTTa_id_of_stableCommonForm_aux a s h

/-- HE→PeTTa on a stable-common atom is a direct fixed point. -/
theorem translateHE_then_translatePeTTa_id_of_stableCommonForm (a : Atom) (s : Nat)
    (h : isStableCommonForm a = true) :
    let (petta, s1) := translateHE a s
    let (he2, _) := translatePeTTa petta s1
    he2 = a := by
  have hhe : translateHE a s = (a, s) := translateHE_id_of_stableCommonForm a s h
  have hpe : translatePeTTa a s = (a, s) := translatePeTTa_id_of_stableCommonForm a s h
  simp [hhe, hpe]

/-- PeTTa→HE on a stable-common atom is a direct fixed point. -/
theorem translatePeTTa_then_translateHE_id_of_stableCommonForm (a : Atom) (s : Nat)
    (h : isStableCommonForm a = true) :
    let (he, s1) := translatePeTTa a s
    let (petta2, _) := translateHE he s1
    petta2 = a := by
  have hpe : translatePeTTa a s = (a, s) := translatePeTTa_id_of_stableCommonForm a s h
  have hhe : translateHE a s = (a, s) := translateHE_id_of_stableCommonForm a s h
  simp [hpe, hhe]

/-- Both translators are identity on the currently formalized shared
    default-atomspace fragment over `&self`. -/
theorem translateHE_id_of_defaultAtomSpaceSharedFragment (a : Atom) (s : Nat)
    (h : isDefaultAtomSpaceSharedFragment a = true) :
    translateHE a s = (a, s) :=
  translateHE_id_of_stableCommonForm a s
    (defaultAtomSpaceSharedFragment_preserves_stableCommonForm a h)

/-- The same fixed-point fact in the PeTTa→HE direction. -/
theorem translatePeTTa_id_of_defaultAtomSpaceSharedFragment (a : Atom) (s : Nat)
    (h : isDefaultAtomSpaceSharedFragment a = true) :
    translatePeTTa a s = (a, s) :=
  translatePeTTa_id_of_stableCommonForm a s
    (defaultAtomSpaceSharedFragment_preserves_stableCommonForm a h)

/-- Both translators are also identity on the broader shared atomspace-handle
    fragment, as soon as the handle itself is already in the stable common
    form. This is the current theorem-backed path toward multi-space support. -/
theorem translateHE_id_of_sharedAtomSpaceFragment (a : Atom) (s : Nat)
    (h : isSharedAtomSpaceFragment a = true) :
    translateHE a s = (a, s) :=
  translateHE_id_of_stableCommonForm a s
    (sharedAtomSpaceFragment_preserves_stableCommonForm a h)

/-- PeTTa→HE direction of the same shared atomspace-handle fixed-point fact. -/
theorem translatePeTTa_id_of_sharedAtomSpaceFragment (a : Atom) (s : Nat)
    (h : isSharedAtomSpaceFragment a = true) :
    translatePeTTa a s = (a, s) :=
  translatePeTTa_id_of_stableCommonForm a s
    (sharedAtomSpaceFragment_preserves_stableCommonForm a h)

/-- Both translators are identity on the shared state fragment
    (`new-state`, `get-state`, `change-state!`) when arguments are already in
    stable common form. -/
theorem translateHE_id_of_sharedStateFragment (a : Atom) (s : Nat)
    (h : isSharedStateFragment a = true) :
    translateHE a s = (a, s) :=
  translateHE_id_of_stableCommonForm a s
    (sharedStateFragment_preserves_stableCommonForm a h)

/-- PeTTa→HE direction of the same shared state fixed-point fact. -/
theorem translatePeTTa_id_of_sharedStateFragment (a : Atom) (s : Nat)
    (h : isSharedStateFragment a = true) :
    translatePeTTa a s = (a, s) :=
  translatePeTTa_id_of_stableCommonForm a s
    (sharedStateFragment_preserves_stableCommonForm a h)

/-- HE→PeTTa fixed-point form specialized to the shared state fragment. -/
theorem translateHE_then_translatePeTTa_id_of_sharedStateFragment (a : Atom) (s : Nat)
    (h : isSharedStateFragment a = true) :
    let (petta, s1) := translateHE a s
    let (he2, _) := translatePeTTa petta s1
    he2 = a :=
  translateHE_then_translatePeTTa_id_of_stableCommonForm a s
    (sharedStateFragment_preserves_stableCommonForm a h)

/-- PeTTa→HE fixed-point form specialized to the shared state fragment. -/
theorem translatePeTTa_then_translateHE_id_of_sharedStateFragment (a : Atom) (s : Nat)
    (h : isSharedStateFragment a = true) :
    let (he, s1) := translatePeTTa a s
    let (petta2, _) := translateHE he s1
    petta2 = a :=
  translatePeTTa_then_translateHE_id_of_stableCommonForm a s
    (sharedStateFragment_preserves_stableCommonForm a h)

/-- First-order `foldall` lowering lands in the stable common fragment as soon
    as the recursively translated goal and init pieces do. -/
theorem translatePeTTa_foldall_preserves_stableCommonForm
    (agg goal init : Atom) (s : Nat)
    (hagg : isFirstOrderReducerAtom agg = true)
    (hgoal : isStableCommonForm (translatePeTTa goal s).1 = true)
    (hinit : isStableCommonForm (translatePeTTa init (translatePeTTa goal s).2).1 = true) :
    isStableCommonForm
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1 = true := by
  obtain ⟨name, rfl⟩ := firstOrderReducerAtom_eq_symbol agg hagg
  have hnot : isForbiddenHeadSymbol (.symbol name) = false := by
    simpa [isFirstOrderReducerAtom] using hagg
  have hhead : isStableCommonHead (.symbol name) = true := by
    simpa [isStableCommonHead, isStableCommonForm] using hnot
  let accVar : Atom :=
    .var ("$__tr_acc_" ++ toString ((translatePeTTa init (translatePeTTa goal s).2).2 + 1 + 1))
  let itemVar : Atom :=
    .var ("$__tr_item_" ++ toString ((translatePeTTa init (translatePeTTa goal s).2).2 + 1 + 1 + 1))
  have happ : isStableCommonForm (.expression [.symbol name, accVar, itemVar]) = true := by
    have hcons := stableCommonForm_cons_of_head (.symbol name) [accVar, itemVar] hhead
    rw [hcons]
    simp [accVar, itemVar, isStableCommonList, isStableCommonForm]
  simp [translatePeTTa, freshVar, isStableCommonForm, isStableCommonExpr,
    isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList, hgoal, hinit,
    hnot, accVar, itemVar, happ]

/-- The lowered first-order `foldall` term is already a fixed point for the
    HE↔PeTTa roundtrip. -/
theorem translatePeTTa_foldall_roundtrip_fixedPoint
    (agg goal init : Atom) (s : Nat)
    (hagg : isFirstOrderReducerAtom agg = true)
    (hgoal : isStableCommonForm (translatePeTTa goal s).1 = true)
    (hinit : isStableCommonForm (translatePeTTa init (translatePeTTa goal s).2).1 = true) :
    let (he, s1) := translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s
    let (petta2, s2) := translateHE he s1
    let (he2, _) := translatePeTTa petta2 s2
    he2 = he := by
  let hs : isStableCommonForm
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1 = true :=
    translatePeTTa_foldall_preserves_stableCommonForm agg goal init s hagg hgoal hinit
  have hhe :
      translateHE
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2
      =
      ((translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1,
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2) :=
    translateHE_id_of_stableCommonForm
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2 hs
  have hpe :
      translatePeTTa
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2
      =
      ((translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1,
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2) :=
    translatePeTTa_id_of_stableCommonForm
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2 hs
  simpa [hs, hhe, hpe]





end Mettapedia.Languages.MeTTa.Translation
