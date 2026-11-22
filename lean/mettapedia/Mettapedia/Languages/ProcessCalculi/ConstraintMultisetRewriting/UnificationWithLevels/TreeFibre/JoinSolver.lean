import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralGroups

/-!
# The join solver: flex–flex equations of one codomain, domains in any order, decided

**Re-reading** (`joinSide`, `joinRereadK_exact`): after the rule of `JoinRule`, with any codomain `m` below both,
the other equations are transported and their sides `λ ȳ. F ȳ` and `λ ȳ. G ȳ` are re-read as `λ ȳ. G ȳ`; every
residual equation is again flex–flex, the re-read unknowns of codomain `m` (`join_viewK`).

**The fragment** (`InJoinFragmentK`): a telescope of families; every equation is a flex–flex equation of families
with several parameters, `λ x̄. F x̄ ≐ λ x̄. G x̄`, whose two unknowns have the same codomain. The domains of the two
unknowns are not required to be comparable.

**The round** reads the first equation and deletes it when both sides are the same unknown; otherwise it applies the
join: `G` is declared again at least upper bounds of the domains, computed by a function on universes, and `F` and the
old `G` are sent to its η-expansion, the other equations re-read.

**Decided** (`joinK_decided`): from some budget on, the tree's driver ends with a principal answer, for every store
of the fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Pointwise joins, computed -/

section Lists

/-- Pointwise joins of two lists of universes, by a join function. -/
def joinsOf (join : Head → Head → Option Head) : List Head → List Head → Option (List Head)
  | [], [] => some []
  | p :: ps, p' :: ps' => (join p p').bind fun w => (joinsOf join ps ps').map fun ws => w :: ws
  | _, _ => none

variable {S : Setting Head L}

theorem joinsOf_sound (join : Head → Head → Option Head)
    (sound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v) :
    ∀ {ps ps' ws : List Head}, joinsOf join ps ps' = some ws → JoinsK S.R ps ps' ws
  | [], [], ws, h => by
      cases h
      exact .nil
  | p :: ps, p' :: ps', ws, h => by
      cases hw : join p p' with
      | none => simp [joinsOf, hw] at h
      | some w =>
          cases hws : joinsOf join ps ps' with
          | none => simp [joinsOf, hw, hws] at h
          | some ws' =>
              simp only [joinsOf, hw, hws, Option.bind_some, Option.map_some] at h
              cases h
              exact .cons (sound hw).1 (sound hw).2 (joinsOf_sound join sound hws)
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

theorem joinsOf_total (join : Head → Head → Option Head)
    (total : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w) :
    ∀ {ps ps' : List Head}, ps.length = ps'.length → AllUniverses S.R ps → AllUniverses S.R ps' →
      ∃ ws, joinsOf join ps ps' = some ws
  | [], [], _, _, _ => ⟨[], rfl⟩
  | p :: ps, p' :: ps', lengths, universes, universes' => by
      obtain ⟨w, hw⟩ := total universes.head universes'.head
      obtain ⟨ws, hws⟩ := joinsOf_total join total (Nat.succ.inj lengths) universes.tail universes'.tail
      exact ⟨w :: ws, by simp [joinsOf, hw, hws]⟩
  | [], _ :: _, lengths, _, _ => by cases lengths
  | _ :: _, [], lengths, _, _ => by cases lengths

theorem JoinsK.length_left {ps ps' ws : List Head} (joins : JoinsK S.R ps ps' ws) : ps.length = ws.length :=
  forall₂_length joins.left

end Lists

/-! ## Re-reading the sides of the joined unknowns -/

section Reread

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- The conditions under which a side `λ ȳ. F ȳ` or `λ ȳ. G ȳ` at `Π (ȳ : U_{p̄'}). U_{q'}` is re-read, after the
rule, as `λ ȳ. G ȳ` with `G` declared at `Π (x̄ : U_{p̄J}). U_m`. -/
def RereadsJ {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (psJ : List Head) (m : Head)
    (side : TotalTerm Θ) (ps' : List Head) (q' : Head) : Prop :=
  side.1.code = famCode ps' q' ∧
    (side.2.code = etaExp ps'.length (.var v.left) ∨ side.2.code = etaExp ps'.length (.var v.right)) ∧
    AllUniverses S.R ps' ∧ S.R.isUniverse q' ∧ List.Forall₂ S.R.cumulative ps' psJ ∧ S.R.cumulative m q'

instance {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (psJ : List Head) (m : Head)
    (side : TotalTerm Θ) (ps' : List Head) (q' : Head) : Decidable (RereadsJ v psJ m side ps' q') := by
  unfold RereadsJ AllUniverses
  infer_instance

/-- The re-read side: `λ ȳ. G ȳ` over the new telescope, at the side's annotation. -/
def rereadTermJ {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (side : TotalTerm Θ) {ps' : List Head}
    {q' : Head} (h : RereadsJ v psJ m side ps' q') :
    Term (joinedMK Θ families v joins hm) (side.1.reindex (joinMKHom Θ families v joins hm lowL lowR)) :=
  ⟨etaExp ps'.length (.var v.right), by
    change Typed S.R (joinedMK Θ families v joins hm).raw (etaExp ps'.length (.var v.right))
      (Presentation.subst (joinKSub v.ps.length v.left v.right) side.1.code)
    rw [h.1, famCode_subst]
    have tG : Typed S.R (joinedMK Θ families v joins hm).raw (.var v.right) (famCode psJ m) := by
      have typed := Derivable.var (R := S.R) (Γ := (joinedMK Θ families v joins hm).raw) v.right
      rw [joinedMK_self] at typed
      exact typed
    exact raisedK_typed h.2.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2 (joinedMK Θ families v joins hm).formed tG⟩

/-- **A side after the rule**: re-read as `λ ȳ. G ȳ` where it is a side of `F` or of `G` at a fitting annotation,
and instantiated otherwise. -/
def joinSide {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (side : TotalTerm Θ) :
    TotalTerm (joinedMK Θ families v joins hm) :=
  match readFam side.1.code with
  | some (ps', q') =>
      if h : RereadsJ v psJ m side ps' q' then
        ⟨side.1.reindex (joinMKHom Θ families v joins hm lowL lowR),
          rereadTermJ families v joins hm lowL lowR side h⟩
      else side.reindex (joinMKHom Θ families v joins hm lowL lowR)
  | none => side.reindex (joinMKHom Θ families v joins hm lowL lowR)

/-- The residual store of the rule. -/
def joinStore {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (rest : EquationStore (TotalTerm Θ)) :
    EquationStore (TotalTerm (joinedMK Θ families v joins hm)) :=
  rest.map fun e' => (joinSide families v joins hm lowL lowR e'.1, joinSide families v joins hm lowL lowR e'.2)

theorem joinSide_cases {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (side : TotalTerm Θ) :
    (∃ ps' q' h, joinSide families v joins hm lowL lowR side =
        ⟨side.1.reindex (joinMKHom Θ families v joins hm lowL lowR),
          rereadTermJ families v joins hm lowL lowR side (ps' := ps') (q' := q') h⟩) ∨
      joinSide families v joins hm lowL lowR side = side.reindex (joinMKHom Θ families v joins hm lowL lowR) := by
  unfold joinSide
  cases hc : readFam side.1.code with
  | none => exact .inr rfl
  | some pq =>
      cases pq with
      | mk ps' q' =>
          by_cases h : RereadsJ v psJ m side ps' q'
          · exact .inl ⟨ps', q', h, dif_pos h⟩
          · exact .inr (dif_neg h)

/-- **The re-read side agrees with the instantiated side** for every solution of the new telescope. -/
theorem joinSide_sound {Θ Δ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)}
    (v : FlexK e) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (side : TotalTerm Θ)
    (g : Δ ⟶ joinedMK Θ families v joins hm) :
    (frames S.levels).E ((joinSide families v joins hm lowL lowR side).reindex g)
      (side.reindex (g ≫ joinMKHom Θ families v joins hm lowL lowR)) := by
  rcases joinSide_cases families v joins hm lowL lowR side with ⟨ps', q', h, isSame⟩ | isSame
  · rw [isSame]
    have tG : Typed S.R Δ.raw (g.substitution v.right) (famCode psJ m) := by
      have typed := g.typed v.right
      rw [joinedMK_self, famCode_subst] at typed
      exact typed
    have lengths : v.ps.length = ps'.length :=
      (lengths_left v).trans (joins.length_left.trans (forall₂_length h.2.2.2.2.1).symm)
    have tEta := raisedK_typed h.2.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2 Δ.formed tG
    refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
    · change TypeEq S.R Δ.raw
        (Presentation.subst g.substitution (Presentation.subst (joinKSub v.ps.length v.left v.right) side.1.code))
        (Presentation.subst (subComp g.substitution (joinKSub v.ps.length v.left v.right)) side.1.code)
      rw [h.1, famCode_subst, famCode_subst, famCode_subst]
      exact (Typed.isType tEta Δ.formed).refl
    · change Equal S.R Δ.raw (Presentation.subst g.substitution (etaExp ps'.length (.var v.right)))
        (Presentation.subst (subComp g.substitution (joinKSub v.ps.length v.left v.right)) side.2.code)
        (Presentation.subst g.substitution (Presentation.subst (joinKSub v.ps.length v.left v.right) side.1.code))
      rw [h.1, famCode_subst, famCode_subst, subst_etaExp]
      rcases h.2.1 with code | code
      · rw [code, subst_etaExp]
        change Equal S.R Δ.raw (etaExp ps'.length (g.substitution v.right))
          (etaExp ps'.length (Presentation.subst g.substitution (joinKSub v.ps.length v.left v.right v.left)))
          (famCode ps' q')
        rw [joinKSub_left, subst_etaExp, lengths]
        exact .symm (etaExp_equal ps' Δ.formed tEta)
      · rw [code, subst_etaExp]
        change Equal S.R Δ.raw (etaExp ps'.length (g.substitution v.right))
          (etaExp ps'.length (Presentation.subst g.substitution (joinKSub v.ps.length v.left v.right v.right)))
          (famCode ps' q')
        rw [joinKSub_right, subst_etaExp, lengths]
        exact .symm (etaExp_equal ps' Δ.formed tEta)
  · rw [isSame, ← ContextualDependentEta.reindex_comp]
    exact ((frames S.levels).equivalence Δ).refl _

/-- A side of `F` or of `G` at a fitting annotation is re-read as `λ ȳ. G ȳ`. -/
theorem joinSide_reread {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) {side : TotalTerm Θ} {ps' : List Head}
    {q' : Head} (h : RereadsJ v psJ m side ps' q') :
    (joinSide families v joins hm lowL lowR side).1.code = famCode ps' q' ∧
      (joinSide families v joins hm lowL lowR side).2.code = etaExp ps'.length (.var v.right) := by
  have candidate : readFam side.1.code = some (ps', q') := by rw [h.1, readFam_famCode]
  have isSame : joinSide families v joins hm lowL lowR side =
      ⟨side.1.reindex (joinMKHom Θ families v joins hm lowL lowR), rereadTermJ families v joins hm lowL lowR side h⟩ := by
    unfold joinSide
    rw [candidate]
    exact dif_pos h
  rw [isSame]
  constructor
  · change Presentation.subst (joinKSub v.ps.length v.left v.right) side.1.code = _
    rw [h.1, famCode_subst]
  · rfl

/-- Any other side is instantiated, and keeps its codes when it mentions neither `F` nor `G`. -/
theorem joinSide_keep {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) {side : TotalTerm Θ} {Z : Fin Θ.arity}
    {ps' : List Head} {q' : Head} (annotation : side.1.code = famCode ps' q')
    (code : side.2.code = etaExp ps'.length (.var Z)) (neL : Z ≠ v.left) (neR : Z ≠ v.right) :
    (joinSide families v joins hm lowL lowR side).1.code = famCode ps' q' ∧
      (joinSide families v joins hm lowL lowR side).2.code = etaExp ps'.length (.var Z) := by
  have notReread : ∀ ps'' q'', ¬ RereadsJ v psJ m side ps'' q'' := by
    intro ps'' q'' h
    obtain ⟨hps, _⟩ := famCode_inj (h.1.symm.trans annotation)
    rcases h.2.1 with codes | codes
    · have codes' := code.symm.trans codes
      rw [hps] at codes'
      exact neL (Tm.var.inj (etaExp_inj _ codes'))
    · have codes' := code.symm.trans codes
      rw [hps] at codes'
      exact neR (Tm.var.inj (etaExp_inj _ codes'))
  rcases joinSide_cases families v joins hm lowL lowR side with ⟨ps'', q'', h, _⟩ | isSame
  · exact absurd h (notReread ps'' q'')
  · rw [isSame]
    constructor
    · change Presentation.subst (joinKSub v.ps.length v.left v.right) side.1.code = _
      rw [annotation, famCode_subst]
    · change Presentation.subst (joinKSub v.ps.length v.left v.right) side.2.code = _
      rw [code, subst_etaExp]
      change etaExp ps'.length (joinKSub v.ps.length v.left v.right Z) = _
      rw [joinKSub_ne _ _ _ neL neR]

/-- Where an unknown is read after the rule: `F` and `G` as the redeclared unknown, the others as themselves. -/
def joinVar {n : Nat} (F G Z : Fin n) : Fin n := if Z = F ∨ Z = G then G else Z

variable (algebra : CumulativeAlgebra S.R)

include algebra in
/-- **The view of an equation after the rule and the re-reading**: flex–flex again, each unknown read through
`joinVar`; a re-read unknown has the codomain `m`, the others keep theirs. -/
theorem join_viewK {Θ : Context S.R} (families : Miller.Families Θ) {e e' : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (w : FlexK e') :
    ∃ t : FlexK ((joinSide families v joins hm lowL lowR e'.1, joinSide families v joins hm lowL lowR e'.2) :
        Equation (TotalTerm (joinedMK Θ families v joins hm))),
      t.left = joinVar v.left v.right w.left ∧ t.right = joinVar v.left v.right w.right ∧
        t.cl = (if w.left = v.left ∨ w.left = v.right then m else w.cl) ∧
        t.cr = (if w.right = v.left ∨ w.right = v.right then m else w.cr) := by
  have side : ∀ (s : TotalTerm Θ) (Z : Fin Θ.arity) (psZ : List Head) (cZ : Head),
      s.1.code = famCode w.ps w.q → s.2.code = etaExp w.ps.length (.var Z) → Ctx.lookup Θ.raw Z = famCode psZ cZ →
      AllUniverses S.R psZ → S.R.isUniverse cZ → List.Forall₂ S.R.cumulative w.ps psZ → S.R.cumulative cZ w.q →
      ∃ (psZ' : List Head) (cZ' : Head), (joinSide families v joins hm lowL lowR s).1.code = famCode w.ps w.q ∧
        (joinSide families v joins hm lowL lowR s).2.code = etaExp w.ps.length (.var (joinVar v.left v.right Z)) ∧
        Ctx.lookup (joinedMK Θ families v joins hm).raw (joinVar v.left v.right Z) = famCode psZ' cZ' ∧
        AllUniverses S.R psZ' ∧ S.R.isUniverse cZ' ∧ List.Forall₂ S.R.cumulative w.ps psZ' ∧
        S.R.cumulative cZ' w.q ∧ cZ' = (if Z = v.left ∨ Z = v.right then m else cZ) := by
    intro s Z psZ cZ annotation code declared upsZ ucZ domain codomain
    by_cases hZ : Z = v.left ∨ Z = v.right
    · have target : joinVar v.left v.right Z = v.right := by
        unfold joinVar
        rw [if_pos hZ]
      have facts : List.Forall₂ S.R.cumulative w.ps psJ ∧ S.R.cumulative m w.q := by
        rcases hZ with hZ | hZ
        · rw [hZ] at declared
          obtain ⟨hps, hc⟩ := famCode_inj (declared.symm.trans v.declared_left)
          rw [hps] at domain
          rw [hc] at codomain
          exact ⟨forall₂_trans algebra.trans domain joins.left, algebra.trans lowL codomain⟩
        · rw [hZ] at declared
          obtain ⟨hps, hc⟩ := famCode_inj (declared.symm.trans v.declared_right)
          rw [hps] at domain
          rw [hc] at codomain
          exact ⟨forall₂_trans algebra.trans domain joins.right, algebra.trans lowR codomain⟩
      have rereads : RereadsJ v psJ m s w.ps w.q := by
        refine ⟨annotation, ?_, w.universes, w.universe_q, facts.1, facts.2⟩
        rcases hZ with hZ | hZ
        · rw [← hZ]
          exact .inl code
        · rw [← hZ]
          exact .inr code
      obtain ⟨same1, same2⟩ := joinSide_reread families v joins hm lowL lowR rereads
      refine ⟨psJ, m, same1, ?_, ?_, joins.universes, hm, facts.1, facts.2, by rw [if_pos hZ]⟩
      · rw [same2, target]
      · rw [target, joinedMK_self]
    · have hL : Z ≠ v.left := fun h => hZ (.inl h)
      have hR : Z ≠ v.right := fun h => hZ (.inr h)
      have target : joinVar v.left v.right Z = Z := by
        unfold joinVar
        rw [if_neg hZ]
      obtain ⟨same1, same2⟩ := joinSide_keep families v joins hm lowL lowR annotation code hL hR
      refine ⟨psZ, cZ, same1, ?_, ?_, upsZ, ucZ, domain, codomain, by rw [if_neg hZ]⟩
      · rw [same2, target]
      · rw [target, joinedMK_ne Θ families v joins hm hR]
        exact declared
  obtain ⟨psl', cl', a1, s1, d1, upl, ucl, dl, cdl, el⟩ := side e'.1 w.left w.psl w.cl w.annotation_left w.side_left
    w.declared_left w.universes_left w.universe_cl w.domain_left w.codomain_left
  obtain ⟨psr', cr', a2, s2, d2, upr, ucr, dr, cdr, er⟩ := side e'.2 w.right w.psr w.cr w.annotation_right
    w.side_right w.declared_right w.universes_right w.universe_cr w.domain_right w.codomain_right
  exact ⟨{
    ps := w.ps
    q := w.q
    left := joinVar v.left v.right w.left
    right := joinVar v.left v.right w.right
    psl := psl'
    cl := cl'
    psr := psr'
    cr := cr'
    annotation_left := a1
    annotation_right := a2
    side_left := s1
    side_right := s2
    declared_left := d1
    declared_right := d2
    universes := w.universes
    universes_left := upl
    universes_right := upr
    universe_q := w.universe_q
    universe_cl := ucl
    universe_cr := ucr
    domain_left := dl
    domain_right := dr
    codomain_left := cdl
    codomain_right := cdr }, rfl, rfl, el, er⟩

end Reread

/-! ## The rule with re-reading, on a whole store -/

section Update

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **The rule with re-reading**: the solved equation is removed, the other equations are transported and their sides
of `F` and `G` re-read as sides of the redeclared unknown. -/
def joinRereadKUpdate {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (forces : JoinForces v psJ m)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := joinedMK Θ families v joins hm
  answer := joinMKHom Θ families v joins hm lowL lowR
  remaining := joinStore families v joins hm lowL lowR rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · exact joinMK_head_solved families v joins hm lowL lowR g
    · have reread := solved _ (List.mem_map.mpr ⟨e', member, rfl⟩)
      exact ((frames S.levels).equivalence Δ).trans
        (((frames S.levels).equivalence Δ).symm (joinSide_sound families v joins hm lowL lowR e'.1 g))
        (((frames S.levels).equivalence Δ).trans reread (joinSide_sound families v joins hm lowL lowR e'.2 g))
  complete := by
    intro Δ f solved
    obtain ⟨g, factored⟩ := joinMK_factors families v joins hm lowL lowR forces f (solved e List.mem_cons_self)
    refine ⟨g, ?_, act_equal_of_substEq S.levels factored⟩
    intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    have solvedRest := solved e' (List.mem_cons_of_mem _ inRest)
    have first := act_equal_of_substEq S.levels factored e'.1
    have second := act_equal_of_substEq S.levels factored e'.2
    have sound₁ := joinSide_sound families v joins hm lowL lowR e'.1 g
    have sound₂ := joinSide_sound families v joins hm lowL lowR e'.2 g
    exact ((frames S.levels).equivalence Δ).trans sound₁
      (((frames S.levels).equivalence Δ).trans (((frames S.levels).equivalence Δ).symm first)
        (((frames S.levels).equivalence Δ).trans solvedRest
          (((frames S.levels).equivalence Δ).trans second (((frames S.levels).equivalence Δ).symm sound₂))))

/-- **The rule with re-reading is exact**, whenever its forcing holds. -/
theorem joinRereadK_exact {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)}
    (v : FlexK e) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (forces : JoinForces v psJ m)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (joinMKHom Θ families v joins hm lowL lowR)
      (joinStore families v joins hm lowL lowR rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨joinRereadKUpdate families v joins hm lowL lowR forces rest, rfl, rfl, rfl⟩

end Update

/-! ## The fragment -/

section Fragment

variable {S : Setting Head L}

/-- **The fragment of the join solver**: families; every equation flex–flex, its two unknowns of one codomain. -/
structure InJoinFragmentK {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : Miller.Families Θ
  shapes : ∀ e ∈ problem, Nonempty (FlexK e)
  codomains : ∀ e ∈ problem, ∀ w : FlexK e, w.cl = w.cr

theorem inJoinFragmentK_delete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InJoinFragmentK (e :: rest)) : InJoinFragmentK rest :=
  ⟨inside.families, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.codomains e' (List.mem_cons_of_mem _ member)⟩

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  (algebra : CumulativeAlgebra S.R)

include algebra in
/-- **The join keeps the fragment.** -/
theorem inJoinFragmentK_join {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InJoinFragmentK (e :: rest)) (v : FlexK e) (same : v.cl = v.cr) {psJ : List Head}
    (joins : JoinsK S.R v.psl v.psr psJ) :
    InJoinFragmentK (joinStore inside.families v joins v.universe_cr (cr_below_cl v same)
      (S.levels.cumulative_refl v.universe_cr) rest) := by
  refine ⟨Miller.redecl_families Θ inside.families v.right psJ v.cr joins.universes v.universe_cr, ?_, ?_⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    obtain ⟨t, _, _, _, _⟩ := join_viewK algebra inside.families v joins v.universe_cr (cr_below_cl v same)
      (S.levels.cumulative_refl v.universe_cr) w
    exact ⟨t⟩
  · intro e'' member u
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    obtain ⟨t, _, _, tcl, tcr⟩ := join_viewK algebra inside.families v joins v.universe_cr (cr_below_cl v same)
      (S.levels.cumulative_refl v.universe_cr) w
    obtain ⟨ul, ur⟩ := FlexK.unique u t
    have cl : u.cl = t.cl := (famCode_inj (u.declared_left.symm.trans (by rw [ul]; exact t.declared_left))).2
    have cr : u.cr = t.cr := (famCode_inj (u.declared_right.symm.trans (by rw [ur]; exact t.declared_right))).2
    -- A re-read unknown was `F` or `G`, of codomain `cr` already.
    have keep : ∀ (Z : Fin Θ.arity) (psZ : List Head) (cZ : Head), Ctx.lookup Θ.raw Z = famCode psZ cZ →
        (if Z = v.left ∨ Z = v.right then v.cr else cZ) = cZ := by
      intro Z psZ cZ declared
      split_ifs with hZ
      · rcases hZ with hZ | hZ
        · rw [hZ] at declared
          exact ((famCode_inj (declared.symm.trans v.declared_left)).2.trans same).symm
        · rw [hZ] at declared
          exact (famCode_inj (declared.symm.trans v.declared_right)).2.symm
      · rfl
    rw [cl, cr, tcl, tcr, keep w.left w.psl w.cl w.declared_left, keep w.right w.psr w.cr w.declared_right]
    exact inside.codomains e' (List.mem_cons_of_mem _ inRest) w

end Fragment

/-! ## The solver -/

section Solver

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)

/-- **One step on a read equation**: delete, or join when the two codomains are the same. -/
def stepJoinK {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  if hsame : v.left = v.right then
    .progress (deleteCodes e (v.annotation_left.trans v.annotation_right.symm)
        (by rw [v.side_left, v.side_right, hsame]) rest)
      (below_of_length (by
        show rest.length < (e :: rest).length
        simp))
  else if hc : v.cl = v.cr then
    match hj : joinsOf join v.psl v.psr with
    | some _ =>
        .progress (joinRereadKUpdate families v (joinsOf_sound join joinSound hj) v.universe_cr (cr_below_cl v hc)
            (S.levels.cumulative_refl v.universe_cr)
            (joinK_forces facts roots heads algebra rigid complete headsTyped v hc (joinsOf_sound join joinSound hj))
            rest)
          (below_of_length (by
            show (joinStore families v (joinsOf_sound join joinSound hj) v.universe_cr (cr_below_cl v hc)
              (S.levels.cumulative_refl v.universe_cr) rest).length < (e :: rest).length
            simp [joinStore]))
    | none => .stuck
  else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def joinRoundK : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels storeRank problem
  | _, [] => .stuck
  | Θ, e :: rest =>
      if hfam : Miller.Families Θ then
        match hd : readFlexK e with
        | some _ => stepJoinK facts roots heads algebra rigid complete headsTyped join joinSound hfam (viewOfK hd) rest
        | none => .stuck
      else .stuck

/-- **The tree's driver with delete and the join.** -/
def joinSolverK : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := joinRoundK facts roots heads algebra rigid complete headsTyped join joinSound

/-- **The rules never refute.** -/
theorem joinRoundK_ne_refuted {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (absent : ¬ (frames S.levels).Solvable problem) :
    joinRoundK facts roots heads algebra rigid complete headsTyped join joinSound problem ≠ .refuted absent := by
  cases problem with
  | nil => intro h; cases h
  | cons e rest =>
      simp only [joinRoundK]
      split_ifs with hfam
      · split
        · unfold stepJoinK
          split_ifs
          · intro h; cases h
          · split
            · intro h; cases h
            · intro h; cases h
          · intro h; cases h
        · intro h; cases h
      · intro h; cases h

/-- **Progress by shape**: on a nonempty store of the fragment, with a total join function, the round is not
stuck. -/
theorem joinRoundK_ne_stuck
    (total : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (inside : InJoinFragmentK problem)
    (nonempty : problem ≠ []) :
    joinRoundK facts roots heads algebra rigid complete headsTyped join joinSound problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      have hd := readFlexK_complete v
      simp only [joinRoundK, dif_pos inside.families]
      split
      · rename_i d hd'
        let w := viewOfK hd'
        have hc : w.cl = w.cr := inside.codomains e List.mem_cons_self w
        have lengths : w.psl.length = w.psr.length := (lengths_left w).symm.trans (lengths_right w)
        obtain ⟨ws, hws⟩ := joinsOf_total join total lengths w.universes_left w.universes_right
        unfold stepJoinK
        split_ifs with h1
        · intro h; cases h
        · split
          · intro h; cases h
          · rename_i hj
            rw [hws] at hj
            cases hj
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem joinRoundK_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InJoinFragmentK problem)
    (progressed : joinRoundK facts roots heads algebra rigid complete headsTyped join joinSound problem =
      .progress update smaller) :
    InJoinFragmentK update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [joinRoundK] at progressed
      split_ifs at progressed with hfam
      split at progressed
      · rename_i d hd
        unfold stepJoinK at progressed
        split_ifs at progressed with h1 h2
        · cases progressed
          exact inJoinFragmentK_delete inside
        · split at progressed
          · rename_i psJ hj
            cases progressed
            exact inJoinFragmentK_join algebra inside (viewOfK hd) h2 (joinsOf_sound join joinSound hj)
          · cases progressed
      · cases progressed

variable (total : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)

/-- **The fragment of the join solver.** -/
def joinFragmentK :
    ContextualDependentWorklist.Fragment
      (joinSolverK facts roots heads algebra rigid complete headsTyped join joinSound) where
  holds := InJoinFragmentK
  stable := fun inside progressed =>
    joinRoundK_stable facts roots heads algebra rigid complete headsTyped join joinSound inside progressed
  decisive := fun inside nonempty =>
    joinRoundK_ne_stuck facts roots heads algebra rigid complete headsTyped join joinSound total inside nonempty

include facts roots heads algebra rigid complete headsTyped joinSound total in
/-- **Decided by shape**: on the join fragment, the tree's driver reaches, at some budget and at every larger one, a
principal answer. Domains need not be comparable. -/
theorem joinK_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InJoinFragmentK original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (joinSolverK facts roots heads algebra rigid complete headsTyped join joinSound) original larger =
          run (joinSolverK facts roots heads algebra rigid complete headsTyped join joinSound) original fuel ∧
        ((∃ state finished,
            run (joinSolverK facts roots heads algebra rigid complete headsTyped join joinSound) original larger =
              .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (joinSolverK facts roots heads algebra rigid complete headsTyped join joinSound) original larger =
              .refuted absent)) :=
  (joinFragmentK facts roots heads algebra rigid complete headsTyped join joinSound total).decided inside

include facts roots heads algebra rigid complete headsTyped joinSound total in
/-- **Every store of the join fragment has a principal answer.** -/
theorem principal_of_inJoinFragmentK {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InJoinFragmentK original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer := by
  obtain ⟨fuel, ends⟩ := joinK_decided facts roots heads algebra rigid complete headsTyped join joinSound total inside
  rcases (ends fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, refuted⟩
  · exact ⟨_, _, principal⟩
  · exact absurd refuted (drive_ne_refuted (joinSolverK facts roots heads algebra rigid complete headsTyped join
      joinSound) (fun problem absent =>
        joinRoundK_ne_refuted facts roots heads algebra rigid complete headsTyped join joinSound problem absent)
      fuel _ absent)

end Solver

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
