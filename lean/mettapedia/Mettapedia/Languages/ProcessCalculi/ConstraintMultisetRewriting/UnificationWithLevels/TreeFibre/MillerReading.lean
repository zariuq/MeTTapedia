import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerIntersection

/-!
# Reading Miller equations from codes

Every reader computes a candidate from the code and then **checks** it by decidable equality of codes, so what it
returns is correct by construction. Each reader also reads every code of its shape (`readFlex_flexSide`,
`readLocal_localSide`, `readEq_isSome`), which is what keeps the fragment of the solver stable.

* `readFam`: the domains and codomain of a universe family.
* `readFlex`: a Miller side `λ ȳ. F y_{img 0} … y_{img (k-1)}`, with `F`'s declared family, the arguments distinct
  (`injective`) and each argument of exactly the universe of `F`'s domain (`domains`).
* `readLocal`: a rigid local `λ ȳ. y_l`.
* `readEq`: an equation at `Π ȳ : U_{qs}. U_d` whose two sides are Miller sides or rigid locals, each typed below
  `U_d`.

Positive examples are the completeness lemmas; negative examples (the same local twice) are in `MillerControls`.
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

/-! ## Decoding -/

section Decoding

/-- The domains and codomain of a universe family. -/
def readFam : {n : Nat} → Tm Head n → Option (List Head × Head)
  | _, .head c => some ([], c)
  | _, .pi (.head p) B => (readFam B).map fun r => (p :: r.1, r.2)
  | _, _ => none

theorem readFam_famCode : ∀ {n : Nat} (ps : List Head) (c : Head), readFam (famCode ps c : Tm Head n) = some (ps, c)
  | _, [], _ => rfl
  | _, p :: ps, c => by
      simp only [famCode_cons, readFam, readFam_famCode ps c, Option.map_some]

/-- Strip one abstraction per binder. -/
def unlams : {n : Nat} → (qs : List Head) → Tm Head n → Option (Tm Head (arity n qs))
  | _, [], t => some t
  | _, _ :: qs, .lam b => unlams qs b
  | _, _ :: _, _ => none

theorem unlams_lams : ∀ {n : Nat} (qs : List Head) (b : Tm Head (arity n qs)), unlams qs (lams qs b) = some b
  | _, [], _ => rfl
  | _, _ :: qs, b => unlams_lams qs b

/-- The head and the arguments of an application spine. -/
def unapps {n : Nat} : Tm Head n → Tm Head n × List (Tm Head n)
  | .app f a => ((unapps f).1, (unapps f).2 ++ [a])
  | t => (t, [])

theorem unapps_apps {n : Nat} : ∀ (ts : List (Tm Head n)) (h : Tm Head n),
    unapps (apps h ts) = ((unapps h).1, (unapps h).2 ++ ts)
  | [], h => by simp [apps]
  | t :: ts, h => by
      show unapps (apps (.app h t) ts) = _
      rw [unapps_apps ts (.app h t)]
      simp [unapps]

theorem mapM_some_map {α β : Type} (g : α → β) : ∀ (l : List α), l.mapM (fun a => some (g a)) = some (l.map g)
  | [] => rfl
  | a :: l => by
      rw [List.mapM_cons, mapM_some_map g l]
      rfl

/-- Universe lists are decided. -/
instance decidableAllUniverses {R : Rules Head} [∀ head, Decidable (R.isUniverse head)] (ps : List Head) :
    Decidable (AllUniverses R ps) := by
  unfold AllUniverses
  infer_instance

variable [DecidableEq Head]

/-- The unknown under the binders. -/
def readUnknown {N : Nat} (qs : List Head) (h : Tm Head (arity N qs)) : Option (Fin N) :=
  (List.finRange N).find? fun F => decide (h = .var (shift qs F))

theorem readUnknown_shift {N : Nat} (qs : List Head) (F : Fin N) :
    readUnknown qs (.var (shift qs F) : Tm Head (arity N qs)) = some F := by
  unfold readUnknown
  cases found : (List.finRange N).find? (fun G => decide ((.var (shift qs F) : Tm Head (arity N qs)) =
      .var (shift qs G))) with
  | none =>
      have missing := List.find?_eq_none.mp found F (List.mem_finRange F)
      simp at missing
  | some G =>
      have hit := List.find?_some found
      simp only [decide_eq_true_eq, Tm.var.injEq] at hit
      rw [shift_injective qs hit]

/-- The local of a variable under the binders. -/
def readLoc {n : Nat} (qs : List Head) (t : Tm Head (arity n qs)) : Option (Fin qs.length) :=
  (List.finRange qs.length).find? fun l => decide (t = .var (loc qs l))

theorem readLoc_loc {n : Nat} (qs : List Head) (l : Fin qs.length) :
    readLoc qs (.var (loc qs l) : Tm Head (arity n qs)) = some l := by
  unfold readLoc
  cases found : (List.finRange qs.length).find? (fun m => decide ((.var (loc qs l) : Tm Head (arity n qs)) =
      .var (loc qs m))) with
  | none =>
      have missing := List.find?_eq_none.mp found l (List.mem_finRange l)
      simp at missing
  | some m =>
      have hit := List.find?_some found
      simp only [decide_eq_true_eq, Tm.var.injEq] at hit
      rw [loc_injective qs hit]

theorem mapM_readLoc {n : Nat} (qs ps : List Head) (img : Fin ps.length → Fin qs.length) :
    (spineArgs (m := arity n qs) ps fun j => loc qs (img j)).mapM (readLoc qs) =
      some ((List.finRange ps.length).map img) := by
  unfold spineArgs
  rw [List.mapM_map]
  have same : (fun j => readLoc (n := n) qs (.var (loc qs (img j)))) = fun j => some (img j) := by
    funext j
    exact readLoc_loc qs (img j)
  rw [Function.comp_def, same, mapM_some_map]

end Decoding

/-! ## Miller sides -/

section Sides

variable [DecidableEq Head]

/-- **A Miller side read from a code**, with the unknown's declared family. -/
structure FlexData {N : Nat} (Γ : Ctx Head N) (qs : List Head) (code : Tm Head N) where
  unknown : Fin N
  ps : List Head
  c : Head
  img : Fin ps.length → Fin qs.length
  side : code = flexSide qs ps unknown img
  declared : Ctx.lookup Γ unknown = famCode ps c
  injective : Function.Injective img
  domains : ∀ j, ps.get j = qs.get (img j)

omit [DecidableEq Head] in
theorem injective_of_nodup {k m : Nat} {ls : List (Fin m)} (hlen : ls.length = k) (nodup : ls.Nodup) :
    Function.Injective fun j : Fin k => ls.get (Fin.cast hlen.symm j) := by
  intro a b same
  have inner := (List.Nodup.get_inj_iff nodup).mp same
  apply Fin.ext
  have := congrArg Fin.val inner
  simpa using this

/-- The final check of a Miller side, once its unknown, family and arguments are read. -/
def checkFlex {N : Nat} (Γ : Ctx Head N) (qs : List Head) (code : Tm Head N) (F : Fin N) (ps : List Head) (c : Head)
    (ls : List (Fin qs.length)) : Option (FlexData Γ qs code) :=
  if hlen : ls.length = ps.length then
    if h : code = flexSide qs ps F (fun j => ls.get (Fin.cast hlen.symm j)) ∧ Ctx.lookup Γ F = famCode ps c ∧
        ls.Nodup ∧ (∀ j : Fin ps.length, ps.get j = qs.get (ls.get (Fin.cast hlen.symm j))) then
      some ⟨F, ps, c, fun j => ls.get (Fin.cast hlen.symm j), h.1, h.2.1, injective_of_nodup hlen h.2.2.1, h.2.2.2⟩
    else none
  else none

/-- **Read a Miller side.** -/
def readFlex {N : Nat} (Γ : Ctx Head N) (qs : List Head) (code : Tm Head N) : Option (FlexData Γ qs code) :=
  match unlams qs code with
  | none => none
  | some body =>
      match readUnknown qs (unapps body).1 with
      | none => none
      | some F =>
          match readFam (Ctx.lookup Γ F) with
          | none => none
          | some r =>
              match (unapps body).2.mapM (readLoc qs) with
              | none => none
              | some ls => checkFlex Γ qs code F r.1 r.2 ls

omit [DecidableEq Head] in
theorem unapps_flexBody {N : Nat} (qs ps : List Head) (F : Fin N) (img : Fin ps.length → Fin qs.length) :
    unapps (flexBody qs ps F img) = (.var (shift qs F), spineArgs ps fun j => loc qs (img j)) := by
  unfold flexBody
  rw [unapps_apps]
  simp [unapps]

theorem checkFlex_isSome {N : Nat} (Γ : Ctx Head N) (qs ps : List Head) (F : Fin N) (c : Head)
    (img : Fin ps.length → Fin qs.length) (declared : Ctx.lookup Γ F = famCode ps c)
    (injective : Function.Injective img) (domains : ∀ j, ps.get j = qs.get (img j)) :
    (checkFlex Γ qs (flexSide qs ps F img) F ps c ((List.finRange ps.length).map img)).isSome = true := by
  have hlen : ((List.finRange ps.length).map img).length = ps.length := by simp
  have back : (fun j : Fin ps.length => ((List.finRange ps.length).map img).get (Fin.cast hlen.symm j)) = img := by
    funext j
    simp
  unfold checkFlex
  rw [dif_pos hlen]
  rw [dif_pos ⟨by rw [back], declared, (List.nodup_finRange _).map injective, fun j => by simpa using domains j⟩]
  rfl

/-- **Every Miller side is read.** -/
theorem readFlex_flexSide {N : Nat} (Γ : Ctx Head N) (qs ps : List Head) (F : Fin N) (c : Head)
    (img : Fin ps.length → Fin qs.length) (declared : Ctx.lookup Γ F = famCode ps c)
    (injective : Function.Injective img) (domains : ∀ j, ps.get j = qs.get (img j)) :
    (readFlex Γ qs (flexSide qs ps F img)).isSome = true := by
  have unl : unlams qs (flexSide qs ps F img) = some (flexBody qs ps F img) := unlams_lams qs _
  unfold readFlex
  rw [unl]
  simp only [unapps_flexBody, readUnknown_shift, declared, readFam_famCode, mapM_readLoc]
  exact checkFlex_isSome Γ qs ps F c img declared injective domains

/-- Read a rigid local. -/
def readLocal {N : Nat} (qs : List Head) (code : Tm Head N) : Option {l : Fin qs.length // code = localSide qs l} :=
  match (List.finRange qs.length).find? fun l => decide (code = localSide qs l) with
  | some l => if h : code = localSide qs l then some ⟨l, h⟩ else none
  | none => none

/-- **Every rigid local is read.** -/
theorem readLocal_localSide {N : Nat} (qs : List Head) (l : Fin qs.length) :
    (readLocal qs (localSide qs l : Tm Head N)).isSome = true := by
  unfold readLocal
  cases found : (List.finRange qs.length).find? (fun m => decide ((localSide qs l : Tm Head N) = localSide qs m)) with
  | none =>
      have missing := List.find?_eq_none.mp found l (List.mem_finRange l)
      simp at missing
  | some m =>
      have hit := List.find?_some found
      simp only [decide_eq_true_eq] at hit
      simp [hit]

end Sides

/-! ## Miller equations -/

section Equations

variable {S : Setting Head L}

/-- **A side of a Miller equation**: a Miller side whose unknown's codomain lies below the annotation's, or a rigid
local whose universe does. -/
inductive SideView {N : Nat} (Γ : Ctx Head N) (qs : List Head) (d : Head) (code : Tm Head N) : Type where
  | flex (data : FlexData Γ qs code) (below : S.R.cumulative data.c d)
  | rigid (l : Fin qs.length) (side : code = localSide qs l) (below : S.R.cumulative (qs.get l) d)

/-- **A Miller equation**: at `Π ȳ : U_{qs}. U_d`, between two sides. -/
structure EqView {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Type where
  qs : List Head
  d : Head
  annotation_left : e.1.1.code = famCode qs d
  annotation_right : e.2.1.code = famCode qs d
  universes : AllUniverses S.R qs
  universe_d : S.R.isUniverse d
  left : SideView (S := S) Θ.raw qs d e.1.2.code
  right : SideView (S := S) Θ.raw qs d e.2.2.code

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- Read a side. -/
def readSide {N : Nat} (Γ : Ctx Head N) (qs : List Head) (d : Head) (code : Tm Head N) :
    Option (SideView (S := S) Γ qs d code) :=
  match readFlex Γ qs code with
  | some data => if h : S.R.cumulative data.c d then some (.flex data h) else none
  | none =>
      match readLocal qs code with
      | some found => if h : S.R.cumulative (qs.get found.1) d then some (.rigid found.1 found.2 h) else none
      | none => none

/-- Read a Miller equation. -/
def readEq {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (EqView (S := S) e) :=
  match readFam e.1.1.code with
  | none => none
  | some r =>
      if h : e.1.1.code = famCode r.1 r.2 ∧ e.2.1.code = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧
          S.R.isUniverse r.2 then
        match readSide (S := S) Θ.raw r.1 r.2 e.1.2.code, readSide (S := S) Θ.raw r.1 r.2 e.2.2.code with
        | some left, some right => some ⟨r.1, r.2, h.1, h.2.1, h.2.2.1, h.2.2.2, left, right⟩
        | _, _ => none
      else none

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem readSide_flex {N : Nat} (Γ : Ctx Head N) (qs ps : List Head) (d : Head) (F : Fin N) (c : Head)
    (img : Fin ps.length → Fin qs.length) (declared : Ctx.lookup Γ F = famCode ps c)
    (injective : Function.Injective img) (domains : ∀ j, ps.get j = qs.get (img j)) (below : S.R.cumulative c d) :
    (readSide (S := S) Γ qs d (flexSide qs ps F img)).isSome = true := by
  unfold readSide
  have read := readFlex_flexSide Γ qs ps F c img declared injective domains
  cases hread : readFlex Γ qs (flexSide qs ps F img) with
  | none => rw [hread] at read; cases read
  | some data =>
      have hF : data.unknown = F := by
        have sides := data.side
        unfold flexSide at sides
        have bodies := congrArg (unlams qs) sides
        rw [unlams_lams, unlams_lams] at bodies
        have heads := congrArg (fun b => (unapps b).1) (Option.some.inj bodies)
        simp only [unapps_flexBody, Tm.var.injEq] at heads
        exact (shift_injective qs heads).symm
      have hc : data.c = c := by
        have same := data.declared
        rw [hF, declared] at same
        exact (famCode_inj same).2.symm
      have below' : S.R.cumulative data.c d := by
        rw [hc]
        exact below
      simp only
      rw [dif_pos below']
      rfl

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem readSide_rigid {N : Nat} (Γ : Ctx Head N) (qs : List Head) (d : Head) (l : Fin qs.length)
    (below : S.R.cumulative (qs.get l) d) : (readSide (S := S) Γ qs d (localSide qs l)).isSome = true := by
  unfold readSide
  cases hflex : readFlex Γ qs (localSide qs l : Tm Head N) with
  | some data =>
      exfalso
      have sides := data.side
      unfold flexSide localSide at sides
      have bodies := congrArg (unlams qs) sides
      rw [unlams_lams, unlams_lams] at bodies
      have heads := congrArg (fun b => (unapps b).1) (Option.some.inj bodies)
      simp only [unapps_flexBody, unapps, Tm.var.injEq] at heads
      exact loc_ne_shift qs l data.unknown heads
  | none =>
      simp only
      have read := readLocal_localSide (N := N) qs l
      cases hl : readLocal qs (localSide qs l : Tm Head N) with
      | none => rw [hl] at read; cases read
      | some found =>
          have same : found.1 = l := by
            have sides := found.2
            unfold localSide at sides
            have bodies := congrArg (unlams qs) sides
            rw [unlams_lams, unlams_lams] at bodies
            exact (loc_injective qs (Tm.var.inj (Option.some.inj bodies))).symm
          have below' : S.R.cumulative (qs.get found.1) d := by
            rw [same]
            exact below
          simp only
          rw [dif_pos below']
          rfl

end Equations

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
