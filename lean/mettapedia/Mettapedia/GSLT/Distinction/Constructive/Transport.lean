import Mettapedia.GSLT.Distinction.Constructive.DepthBound

/-!
# Transport of depth-indexed values along observation maps, with errors

The constructive form of the requirements of `Isometry.ObservationBisimulation`
between presented systems on one value scale: a term map respecting the
equations, translations of observation names and labels, labelled steps
preserved, labelled steps leaving an image lifted up to the target equations.
Readings may move by a declared **error** (`ObservationMap`); an exact map has
error `0`.

* **Forward transport** (`abs_val_translate_sub_le`): every translated formula
  moves by at most the error, uniformly in its depth, since the discount does
  not enlarge differences.  Exact maps preserve values (`val_translate`).
* **Supplied sections** (`VocabularySection`): where the classical theorem
  pulls a target formula back through `Function.surjInv`, here an inverse of
  the observation and label translations is data.  Pulled-back formulas move
  by at most the error (`abs_val_pullback_sub_le`); with a section the depth
  bounds of mapped pairs move by at most twice the error at every depth
  (`abs_depthBound_map_sub_le`), and exact maps preserve them
  (`depthBound_map_eq`).  Without a section only the one-sided inequality holds
  (`depthBound_le_map`); `Controls` shows the other side failing.
* **Sections from enumerations** (`VocabularySection.ofEnumeration`): for a
  listed source vocabulary and decidable equality of target names, a section is
  computed from surjectivity by search, without choice.
* **Errors add** (`ObservationMap.comp`, `DepthDistortion.comp`): composite
  maps carry the sum of the errors, and depth distortions add.

A positive error bound gives no exact equality of values, and no exact
dependent transport; `Controls` exhibits a composite whose error is attained.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Constructive

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner

universe uS uT uU uA uL uO uA' uL' uO' uA'' uL'' uO'' uV

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

set_option linter.checkUnivs false in
/-- An **observation map with error** between presented systems on one scale:
the equations and labelled steps are preserved, labelled steps leaving an image
lift up to the target equations, and readings move by at most `error`. -/
structure ObservationMap {S : GSLT.{uS}} {T : GSLT.{uT}} {K : Scale V}
    (Q : PresentedSystem.{uS, uA, uL, uO} S K) (R : PresentedSystem.{uT, uA', uL', uO'} T K)
    (error : V) where
  error_nonneg : 0 ≤ error
  /-- The term map. -/
  mapTerm : S.Term → T.Term
  mapEquiv : ∀ {left right : S.Term}, S.Equiv left right →
    T.Equiv (mapTerm left) (mapTerm right)
  /-- The translation of observation names. -/
  atom : Q.Obs → R.Obs
  /-- The translation of labels. -/
  label : Q.dynamics.Label → R.dynamics.Label
  value_close : ∀ observation term,
    |R.value (atom observation) (mapTerm term) - Q.value observation term| ≤ error
  mapAct : ∀ step ⦃term target : S.Term⦄, Q.dynamics.act step term target →
    R.dynamics.act (label step) (mapTerm term) (mapTerm target)
  liftAct : ∀ step ⦃term : S.Term⦄ ⦃target' : T.Term⦄,
    R.dynamics.act (label step) (mapTerm term) target' →
      ∃ target, Q.dynamics.act step term target ∧ T.Equiv (mapTerm target) target'

namespace ObservationMap

variable {S : GSLT.{uS}} {T : GSLT.{uT}} {K : Scale V}
  {Q : PresentedSystem.{uS, uA, uL, uO} S K} {R : PresentedSystem.{uT, uA', uL', uO'} T K}
  {error : V} (map : ObservationMap Q R error)

/-! ## Formulas forward -/

/-- Translate a formula along the vocabulary maps; thresholds are kept. -/
def translate : Q.Formula → R.Formula
  | .top => .top
  | .atom observation => .atom (map.atom observation)
  | .neg inner => .neg (translate inner)
  | .conj left right => .conj (translate left) (translate right)
  | .shift threshold inner => .shift threshold (translate inner)
  | .dia step inner => .dia (map.label step) (translate inner)

theorem depth_translate : ∀ formula : Q.Formula, (map.translate formula).depth = formula.depth
  | .top => rfl
  | .atom _ => rfl
  | .neg inner => depth_translate inner
  | .conj left right => by
      simp only [translate, ScaledFormula.depth, depth_translate left, depth_translate right]
  | .shift _ inner => depth_translate inner
  | .dia _ inner => by simp only [translate, ScaledFormula.depth, depth_translate inner]

/-- **The diamond step of transport.** If two inner formulas are within the
error along the map, so are their diamonds. -/
theorem abs_dia_sub_le (step : Q.dynamics.Label) (inner : Q.Formula) (inner' : R.Formula)
    (close : ∀ term, |R.val inner' (map.mapTerm term) - Q.val inner term| ≤ error)
    (term : S.Term) :
    |R.val (.dia (map.label step) inner') (map.mapTerm term) - Q.val (.dia step inner) term| ≤
      error := by
  rw [R.val_dia, Q.val_dia, ← K.discount_sub, K.abs_discount]
  refine (K.discount_le (abs_nonneg _)).trans ?_
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  constructor
  · refine listSup_le_listSup_add _ _ map.error_nonneg fun target' member => ?_
    obtain ⟨target, sourceStep, equivalent⟩ := map.liftAct step (R.successors_act member)
    obtain ⟨representative, representativeMember, close'⟩ := Q.successors_cover sourceStep
    refine ⟨representative, representativeMember, ?_⟩
    rw [← R.val_resp inner' equivalent, ← Q.val_resp inner close']
    exact sub_le_iff_le_add'.mp (abs_sub_le_iff.mp (close target)).1
  · refine listSup_le_listSup_add _ _ map.error_nonneg fun target member => ?_
    obtain ⟨representative, representativeMember, close'⟩ :=
      R.successors_cover (map.mapAct step (Q.successors_act member))
    refine ⟨representative, representativeMember, ?_⟩
    rw [← R.val_resp inner' close']
    exact sub_le_iff_le_add'.mp (abs_sub_le_iff.mp (close target)).2

/-- **Forward transport.** A translated formula moves by at most the error,
at every depth. -/
theorem abs_val_translate_sub_le : ∀ (formula : Q.Formula) (term : S.Term),
    |R.val (map.translate formula) (map.mapTerm term) - Q.val formula term| ≤ error
  | .top, _ => by
      show |R.val .top _ - Q.val .top _| ≤ error
      rw [R.val_top, Q.val_top, sub_self, abs_zero]
      exact map.error_nonneg
  | .atom observation, term => map.value_close observation term
  | .neg inner, term => by
      show |R.val (.neg (map.translate inner)) _ - Q.val (.neg inner) _| ≤ error
      rw [R.val_neg, Q.val_neg, show K.one - R.val (map.translate inner) (map.mapTerm term) -
        (K.one - Q.val inner term) = Q.val inner term - R.val (map.translate inner) (map.mapTerm term)
        by abel, abs_sub_comm]
      exact abs_val_translate_sub_le inner term
  | .conj first second, term => by
      show |R.val (.conj (map.translate first) (map.translate second)) _ -
        Q.val (.conj first second) _| ≤ error
      rw [R.val_conj, Q.val_conj]
      exact (abs_min_sub_min_le _ _ _ _).trans
        (max_le (abs_val_translate_sub_le first term) (abs_val_translate_sub_le second term))
  | .shift threshold inner, term => by
      show |R.val (.shift threshold (map.translate inner)) _ - Q.val (.shift threshold inner) _| ≤
        error
      rw [R.val_shift, Q.val_shift]
      refine (K.abs_clamp_sub_clamp_le _ _).trans ?_
      rw [sub_sub_sub_cancel_right]
      exact abs_val_translate_sub_le inner term
  | .dia step inner, term =>
      map.abs_dia_sub_le step inner (map.translate inner)
        (fun term => abs_val_translate_sub_le inner term) term

/-- **Exact maps preserve formula values.** -/
theorem val_translate (map : ObservationMap Q R 0) (formula : Q.Formula) (term : S.Term) :
    R.val (map.translate formula) (map.mapTerm term) = Q.val formula term :=
  eq_of_abs_sub_nonpos (map.abs_val_translate_sub_le formula term)

/-- **No loss beyond the error.** The depth bound of a pair is at most that of
its image plus twice the error.  No section is needed. -/
theorem depthBound_le_map (WQ : Q.Vocabulary) (WR : R.Vocabulary) (depth : ℕ)
    (left right : S.Term) :
    Q.depthBound WQ depth left right ≤
      R.depthBound WR depth (map.mapTerm left) (map.mapTerm right) + (error + error) := by
  obtain ⟨formula, formulaDepth, attained⟩ := Q.exists_formula_eq_depthBound WQ depth left right
  rw [← attained]
  have leftClose := abs_sub_le_iff.mp (map.abs_val_translate_sub_le formula left)
  have rightClose := abs_sub_le_iff.mp (map.abs_val_translate_sub_le formula right)
  have translatedDepth : (map.translate formula).depth ≤ depth := by
    rw [map.depth_translate]; exact formulaDepth
  calc Q.val formula left - Q.val formula right
      ≤ (R.val (map.translate formula) (map.mapTerm left) + error) -
          (R.val (map.translate formula) (map.mapTerm right) - error) :=
        sub_le_sub (sub_le_iff_le_add'.mp leftClose.2) (sub_le_comm.mp rightClose.1)
    _ = (R.val (map.translate formula) (map.mapTerm left) -
          R.val (map.translate formula) (map.mapTerm right)) + (error + error) := by abel
    _ ≤ R.depthBound WR depth (map.mapTerm left) (map.mapTerm right) + (error + error) :=
        add_le_add ((le_abs_self _).trans
          (R.abs_val_sub_le_depthBound WR _ depth _ _ translatedDepth)) le_rfl

/-! ## Formulas back, along supplied sections -/

/-- **A supplied vocabulary section**: right inverses of the observation-name
and label translations, given as data. -/
structure VocabularySection where
  atomBack : R.Obs → Q.Obs
  atom_atomBack : ∀ observation, map.atom (atomBack observation) = observation
  labelBack : R.dynamics.Label → Q.dynamics.Label
  label_labelBack : ∀ step, map.label (labelBack step) = step

variable {map}

/-- Pull a target formula back along a supplied section. -/
def pullback (section' : map.VocabularySection) : R.Formula → Q.Formula
  | .top => .top
  | .atom observation => .atom (section'.atomBack observation)
  | .neg inner => .neg (pullback section' inner)
  | .conj left right => .conj (pullback section' left) (pullback section' right)
  | .shift threshold inner => .shift threshold (pullback section' inner)
  | .dia step inner => .dia (section'.labelBack step) (pullback section' inner)

theorem depth_pullback (section' : map.VocabularySection) :
    ∀ formula : R.Formula, (pullback section' formula).depth = formula.depth
  | .top => rfl
  | .atom _ => rfl
  | .neg inner => depth_pullback section' inner
  | .conj left right => by
      simp only [pullback, ScaledFormula.depth, depth_pullback section' left,
        depth_pullback section' right]
  | .shift _ inner => depth_pullback section' inner
  | .dia _ inner => by simp only [pullback, ScaledFormula.depth, depth_pullback section' inner]

/-- **Pullback transport.** A pulled-back formula moves by at most the error. -/
theorem abs_val_pullback_sub_le (section' : map.VocabularySection) :
    ∀ (formula : R.Formula) (term : S.Term),
      |R.val formula (map.mapTerm term) - Q.val (pullback section' formula) term| ≤ error
  | .top, _ => by
      show |R.val .top _ - Q.val .top _| ≤ error
      rw [R.val_top, Q.val_top, sub_self, abs_zero]
      exact map.error_nonneg
  | .atom observation, term => by
      have close := map.value_close (section'.atomBack observation) term
      rwa [section'.atom_atomBack] at close
  | .neg inner, term => by
      show |R.val (.neg inner) _ - Q.val (.neg (pullback section' inner)) _| ≤ error
      rw [R.val_neg, Q.val_neg, show K.one - R.val inner (map.mapTerm term) -
        (K.one - Q.val (pullback section' inner) term) =
          Q.val (pullback section' inner) term - R.val inner (map.mapTerm term) by abel,
        abs_sub_comm]
      exact abs_val_pullback_sub_le section' inner term
  | .conj first second, term => by
      show |R.val (.conj first second) _ -
        Q.val (.conj (pullback section' first) (pullback section' second)) _| ≤ error
      rw [R.val_conj, Q.val_conj]
      exact (abs_min_sub_min_le _ _ _ _).trans
        (max_le (abs_val_pullback_sub_le section' first term)
          (abs_val_pullback_sub_le section' second term))
  | .shift threshold inner, term => by
      show |R.val (.shift threshold inner) _ - Q.val (.shift threshold (pullback section' inner)) _| ≤
        error
      rw [R.val_shift, Q.val_shift]
      refine (K.abs_clamp_sub_clamp_le _ _).trans ?_
      rw [sub_sub_sub_cancel_right]
      exact abs_val_pullback_sub_le section' inner term
  | .dia step inner, term => by
      have close := map.abs_dia_sub_le (section'.labelBack step) (pullback section' inner) inner
        (fun term => abs_val_pullback_sub_le section' inner term) term
      rwa [section'.label_labelBack] at close

/-- With a section, the depth bound of an image pair is at most that of the
pair plus twice the error. -/
theorem depthBound_map_le (section' : map.VocabularySection) (WQ : Q.Vocabulary)
    (WR : R.Vocabulary) (depth : ℕ) (left right : S.Term) :
    R.depthBound WR depth (map.mapTerm left) (map.mapTerm right) ≤
      Q.depthBound WQ depth left right + (error + error) := by
  obtain ⟨formula, formulaDepth, attained⟩ :=
    R.exists_formula_eq_depthBound WR depth (map.mapTerm left) (map.mapTerm right)
  rw [← attained]
  have leftClose := abs_sub_le_iff.mp (abs_val_pullback_sub_le section' formula left)
  have rightClose := abs_sub_le_iff.mp (abs_val_pullback_sub_le section' formula right)
  have pulledDepth : (pullback section' formula).depth ≤ depth := by
    rw [depth_pullback]; exact formulaDepth
  calc R.val formula (map.mapTerm left) - R.val formula (map.mapTerm right)
      ≤ (Q.val (pullback section' formula) left + error) -
          (Q.val (pullback section' formula) right - error) :=
        sub_le_sub (sub_le_iff_le_add'.mp leftClose.1) (sub_le_comm.mp rightClose.2)
    _ = (Q.val (pullback section' formula) left - Q.val (pullback section' formula) right) +
          (error + error) := by abel
    _ ≤ Q.depthBound WQ depth left right + (error + error) :=
        add_le_add ((le_abs_self _).trans
          (Q.abs_val_sub_le_depthBound WQ _ depth _ _ pulledDepth)) le_rfl

/-- **Depth bounds transport within twice the error, at every depth.** -/
theorem abs_depthBound_map_sub_le (section' : map.VocabularySection) (WQ : Q.Vocabulary)
    (WR : R.Vocabulary) (depth : ℕ) (left right : S.Term) :
    |R.depthBound WR depth (map.mapTerm left) (map.mapTerm right) - Q.depthBound WQ depth left right| ≤
      error + error := by
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  exact ⟨depthBound_map_le section' WQ WR depth left right,
    map.depthBound_le_map WQ WR depth left right⟩

/-- **Exact maps with a section preserve the depth bounds.** -/
theorem depthBound_map_eq {map : ObservationMap Q R 0} (section' : map.VocabularySection)
    (WQ : Q.Vocabulary) (WR : R.Vocabulary) (depth : ℕ) (left right : S.Term) :
    R.depthBound WR depth (map.mapTerm left) (map.mapTerm right) = Q.depthBound WQ depth left right :=
  eq_of_abs_sub_nonpos (by
    have := abs_depthBound_map_sub_le section' WQ WR depth left right
    rwa [add_zero] at this)

/-! ## Sections computed from enumerations -/

theorem find?_isSome_of_surjective {α : Type uA} {β : Type uO} [DecidableEq β] (f : α → β)
    (list : List α) (complete : ∀ element, element ∈ list)
    (surjective : ∀ image, ∃ element, f element = image) (image : β) :
    (list.find? fun element => decide (f element = image)).isSome := by
  obtain ⟨element, same⟩ := surjective image
  exact List.find?_isSome.mpr ⟨element, complete element, decide_eq_true same⟩

/-- Search a complete list for a preimage. -/
def preimageOf {α : Type uA} {β : Type uO} [DecidableEq β] (f : α → β) (list : List α)
    (complete : ∀ element, element ∈ list) (surjective : ∀ image, ∃ element, f element = image)
    (image : β) : α :=
  (list.find? fun element => decide (f element = image)).get
    (find?_isSome_of_surjective f list complete surjective image)

theorem preimageOf_spec {α : Type uA} {β : Type uO} [DecidableEq β] (f : α → β) (list : List α)
    (complete : ∀ element, element ∈ list) (surjective : ∀ image, ∃ element, f element = image)
    (image : β) : f (preimageOf f list complete surjective image) = image := by
  have member : preimageOf f list complete surjective image ∈
      list.find? (fun element => decide (f element = image)) :=
    Option.get_mem (find?_isSome_of_surjective f list complete surjective image)
  have found : decide (f (preimageOf f list complete surjective image) = image) = true :=
    List.find?_some (p := fun element => decide (f element = image)) member
  exact of_decide_eq_true found

/-- **A section from an enumeration**: a listed source vocabulary and
decidable equality of target names compute a section from surjectivity. -/
def VocabularySection.ofEnumeration (map : ObservationMap Q R error) (WQ : Q.Vocabulary)
    [DecidableEq R.Obs] [DecidableEq R.dynamics.Label]
    (atomSurjective : ∀ observation, ∃ observation', map.atom observation' = observation)
    (labelSurjective : ∀ step, ∃ step', map.label step' = step) : map.VocabularySection where
  atomBack := preimageOf map.atom WQ.observations WQ.observations_complete atomSurjective
  atom_atomBack := preimageOf_spec _ _ _ _
  labelBack := preimageOf map.label WQ.labels WQ.labels_complete labelSurjective
  label_labelBack := preimageOf_spec _ _ _ _

end ObservationMap

/-! ## Identity and composition: errors add -/

namespace ObservationMap

variable {S : GSLT.{uS}} {T : GSLT.{uT}} {U : GSLT.{uU}} {K : Scale V}
  {Q : PresentedSystem.{uS, uA, uL, uO} S K} {R : PresentedSystem.{uT, uA', uL', uO'} T K}
  {P : PresentedSystem.{uU, uA'', uL'', uO''} U K}

/-- The identity map, with error `0`. -/
def identity (Q : PresentedSystem.{uS, uA, uL, uO} S K) : ObservationMap Q Q 0 where
  error_nonneg := le_rfl
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  atom := id
  label := id
  value_close _ _ := by rw [id, id, sub_self, abs_zero]
  mapAct _ _ _ step := step
  liftAct _ _ target step := ⟨target, step, S.equations.iseqv.refl _⟩

/-- **Composition adds the errors.** -/
def comp {first second : V} (earlier : ObservationMap Q R first) (later : ObservationMap R P second) :
    ObservationMap Q P (first + second) where
  error_nonneg := add_nonneg earlier.error_nonneg later.error_nonneg
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  atom := later.atom ∘ earlier.atom
  label := later.label ∘ earlier.label
  value_close observation term := by
    simp only [Function.comp_apply]
    calc |P.value (later.atom (earlier.atom observation)) (later.mapTerm (earlier.mapTerm term)) -
          Q.value observation term|
        = |(P.value (later.atom (earlier.atom observation)) (later.mapTerm (earlier.mapTerm term)) -
            R.value (earlier.atom observation) (earlier.mapTerm term)) +
          (R.value (earlier.atom observation) (earlier.mapTerm term) - Q.value observation term)| := by
          rw [sub_add_sub_cancel]
      _ ≤ second + first := (abs_add_le _ _).trans
          (add_le_add (later.value_close _ _) (earlier.value_close _ _))
      _ = first + second := add_comm _ _
  mapAct step _ _ sourceStep := later.mapAct _ (earlier.mapAct step sourceStep)
  liftAct step term target'' targetStep := by
    obtain ⟨middle, middleStep, middleClose⟩ := later.liftAct _ targetStep
    obtain ⟨target, sourceStep, sourceClose⟩ := earlier.liftAct step middleStep
    exact ⟨target, sourceStep, U.equations.iseqv.trans (later.mapEquiv sourceClose) middleClose⟩

/-- Sections compose. -/
def VocabularySection.comp {first second : V} {earlier : ObservationMap Q R first}
    {later : ObservationMap R P second} (earlierSection : earlier.VocabularySection)
    (laterSection : later.VocabularySection) : (earlier.comp later).VocabularySection where
  atomBack := earlierSection.atomBack ∘ laterSection.atomBack
  atom_atomBack observation := by
    show later.atom (earlier.atom (earlierSection.atomBack (laterSection.atomBack observation))) = _
    rw [earlierSection.atom_atomBack, laterSection.atom_atomBack]
  labelBack := earlierSection.labelBack ∘ laterSection.labelBack
  label_labelBack step := by
    show later.label (earlier.label (earlierSection.labelBack (laterSection.labelBack step))) = _
    rw [earlierSection.label_labelBack, laterSection.label_labelBack]

end ObservationMap

/-! ## Depth distortion -/

/-- A term map **distorts the depth bounds by at most** `bound` when, at every
depth, the bound of each image pair is within `bound` of the bound of the pair. -/
def DepthDistortion {S : GSLT.{uS}} {T : GSLT.{uT}} {K : Scale V}
    {Q : PresentedSystem.{uS, uA, uL, uO} S K} {R : PresentedSystem.{uT, uA', uL', uO'} T K}
    (WQ : Q.Vocabulary) (WR : R.Vocabulary) (mapTerm : S.Term → T.Term) (bound : V) : Prop :=
  ∀ (depth : ℕ) (left right : S.Term),
    |R.depthBound WR depth (mapTerm left) (mapTerm right) - Q.depthBound WQ depth left right| ≤ bound

namespace DepthDistortion

variable {S : GSLT.{uS}} {T : GSLT.{uT}} {U : GSLT.{uU}} {K : Scale V}
  {Q : PresentedSystem.{uS, uA, uL, uO} S K} {R : PresentedSystem.{uT, uA', uL', uO'} T K}
  {P : PresentedSystem.{uU, uA'', uL'', uO''} U K}
  {WQ : Q.Vocabulary} {WR : R.Vocabulary} {WP : P.Vocabulary}

/-- **Depth distortions add under composition.** -/
theorem comp {first second : V} {earlier : S.Term → T.Term} {later : T.Term → U.Term}
    (earlierBound : DepthDistortion WQ WR earlier first)
    (laterBound : DepthDistortion WR WP later second) :
    DepthDistortion WQ WP (later ∘ earlier) (first + second) := by
  intro depth left right
  calc |P.depthBound WP depth (later (earlier left)) (later (earlier right)) -
        Q.depthBound WQ depth left right|
      = |(P.depthBound WP depth (later (earlier left)) (later (earlier right)) -
            R.depthBound WR depth (earlier left) (earlier right)) +
          (R.depthBound WR depth (earlier left) (earlier right) - Q.depthBound WQ depth left right)| := by
        rw [sub_add_sub_cancel]
    _ ≤ second + first := (abs_add_le _ _).trans
        (add_le_add (laterBound depth _ _) (earlierBound depth left right))
    _ = first + second := add_comm _ _

end DepthDistortion

/-- **A map with a section distorts the depth bounds by at most twice its
error.** -/
theorem ObservationMap.depthDistortion {S : GSLT.{uS}} {T : GSLT.{uT}} {K : Scale V}
    {Q : PresentedSystem.{uS, uA, uL, uO} S K} {R : PresentedSystem.{uT, uA', uL', uO'} T K}
    {error : V} {map : ObservationMap Q R error} (section' : map.VocabularySection)
    (WQ : Q.Vocabulary) (WR : R.Vocabulary) :
    DepthDistortion WQ WR map.mapTerm (error + error) :=
  fun depth left right => ObservationMap.abs_depthBound_map_sub_le section' WQ WR depth left right

end Mettapedia.GSLT.Distinction.Constructive
