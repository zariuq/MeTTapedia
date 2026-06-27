/-
Module: Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
Layer: Bridge / canonical hub (Layer M — metavariable α)

Keystone of the canonical-hub architecture: an *injective renaming is inert under*
`Metta.canonicalizeVars`. MeTTa rule variables are first-order query variables, so every engine's
"freshening" (HE `#idx`, LeaTTa runtime `#counter`, CeTTa `$z#1`, the HE oracle `$X#33`) is just an
injective renaming. Therefore each engine is *canon-stable*: its result's canonical form depends only on
the raw rule, not on the fresh-name choice. Cross-engine agreement then factors through the canonical
core (`AlphaEquivalent` = equal `canonicalizeVars`) with no counter-matching.

Core crux: `canonicalizeVars_renBy_of_injective`. Backbone: a total-function renamer `renBy` that
composes cleanly (the list-based `Metta.renameVars` does not).
-/
import MettaHyperonFull.Core.Alpha
import MettaHyperonFull.Proofs.Basic
import MettaHyperonFull.Proofs.Alpha
import Mathlib

namespace Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening

open Metta

/-! ## §1  `renBy`: rename every variable by a total function (clean composition) -/

/-- Rename every variable of an atom by a total function `f`. Unlike the list-based
    `Metta.renameVars`, this composes cleanly. -/
def renBy (f : VarName → VarName) : Atom → Atom
  | Atom.sym s => Atom.sym s
  | Atom.var v => Atom.var (f v)
  | Atom.gnd g => Atom.gnd g
  | Atom.expr xs => Atom.expr (xs.map (renBy f))

/-- The total function that `Metta.renameVars m` induces on variable leaves. -/
def applyRen (m : List (VarName × VarName)) (v : VarName) : VarName :=
  ((m.find? (·.1 == v)).map (·.2)).getD v

@[simp] theorem renBy_var (f : VarName → VarName) (v : VarName) :
    renBy f (Atom.var v) = Atom.var (f v) := by simp [renBy]

@[simp] theorem renBy_expr (f : VarName → VarName) (xs : List Atom) :
    renBy f (Atom.expr xs) = Atom.expr (xs.map (renBy f)) := by simp [renBy]

/-- `Metta.renameVars` is `renBy` of the induced leaf function. -/
theorem renameVars_eq_renBy (m : List (VarName × VarName)) (a : Atom) :
    Metta.renameVars m a = renBy (applyRen m) a := by
  induction a with
  | expr xs ih =>
      simp only [Metta.renameVars, renBy_expr]
      exact congrArg Atom.expr (List.map_congr_left ih)
  | _ => simp [Metta.renameVars, renBy, applyRen]

/-- `renBy` composes: renaming by `g` then `f` is renaming by `f ∘ g`. -/
theorem renBy_comp (f g : VarName → VarName) (a : Atom) :
    renBy f (renBy g a) = renBy (fun v => f (g v)) a := by
  induction a with
  | expr xs ih =>
      simp only [renBy_expr, List.map_map]
      exact congrArg Atom.expr (List.map_congr_left ih)
  | _ => simp [renBy]

/-- `renBy` acts on the variable list by mapping `f` over it. -/
theorem renBy_vars (f : VarName → VarName) (a : Atom) :
    (renBy f a).vars = a.vars.map f := by
  induction a with
  | expr xs ih =>
      simp only [renBy_expr, Atom.vars, List.map_map]
      rw [List.map_flatten, List.map_map]
      exact congrArg List.flatten (List.map_congr_left ih)
  | _ => simp [renBy, Atom.vars]

/-- If `f` and `g` agree on every variable occurring in `a`, they rename `a` identically. -/
theorem renBy_congr {f g : VarName → VarName} {a : Atom}
    (h : ∀ v ∈ a.vars, f v = g v) : renBy f a = renBy g a := by
  induction a with
  | var v => simp only [renBy_var]; exact congrArg Atom.var (h v (by simp [Atom.vars]))
  | expr xs ih =>
      simp only [renBy_expr]
      refine congrArg Atom.expr (List.map_congr_left ?_)
      intro x hx
      refine ih x hx (fun v hv => h v ?_)
      simp only [Atom.vars, List.mem_flatten, List.mem_map]
      exact ⟨x.vars, ⟨x, hx, rfl⟩, hv⟩
  | _ => simp [renBy]

/-! ## §2  `distinctVarsAux`: membership, nodup, commutation with injective maps -/

theorem mem_distinctVarsAux (xs seen : List VarName) (v : VarName) :
    v ∈ distinctVarsAux xs seen ↔ v ∈ xs ∧ v ∉ seen := by
  induction xs generalizing seen with
  | nil => simp [distinctVarsAux]
  | cons x xs ih =>
    rw [distinctVarsAux]
    by_cases hx : x ∈ seen
    · rw [if_pos (by simpa [List.contains_eq_mem] using hx), ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.mp h1 with rfl | h1
        · exact absurd hx h2
        · exact ⟨h1, h2⟩
    · rw [if_neg (by simpa [List.contains_eq_mem] using hx), List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by simp, hx⟩
        · exact ⟨List.mem_cons_of_mem _ h1, fun h => h2 (List.mem_cons_of_mem _ h)⟩
      · rintro ⟨h1, h2⟩
        by_cases hvx : v = x
        · exact Or.inl hvx
        · have hxs : v ∈ xs := (List.mem_cons.mp h1).resolve_left hvx
          exact Or.inr ⟨hxs, by simp only [List.mem_cons, not_or]; exact ⟨hvx, h2⟩⟩

theorem distinctVarsAux_nodup (xs seen : List VarName) :
    (distinctVarsAux xs seen).Nodup := by
  induction xs generalizing seen with
  | nil => simp [distinctVarsAux]
  | cons x xs ih =>
    rw [distinctVarsAux]
    by_cases hx : x ∈ seen
    · rw [if_pos (by simpa [List.contains_eq_mem] using hx)]; exact ih seen
    · rw [if_neg (by simpa [List.contains_eq_mem] using hx), List.nodup_cons]
      refine ⟨?_, ih (x :: seen)⟩
      rw [mem_distinctVarsAux]
      rintro ⟨_, h2⟩
      exact h2 (by simp)

/-- An injective renaming commutes with first-occurrence deduplication. -/
theorem distinctVarsAux_map_injOn {g : VarName → VarName}
    (xs seen : List VarName)
    (hg : Set.InjOn g {v | v ∈ xs ∨ v ∈ seen}) :
    distinctVarsAux (xs.map g) (seen.map g) = (distinctVarsAux xs seen).map g := by
  induction xs generalizing seen with
  | nil => simp [distinctVarsAux]
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [distinctVarsAux, distinctVarsAux]
    have hiff : (seen.map g).contains (g x) = seen.contains x := by
      simp only [List.contains_eq_mem, decide_eq_decide, List.mem_map]
      constructor
      · rintro ⟨y, hy, hgy⟩
        exact (hg (by exact Or.inr hy) (by exact Or.inl (by simp)) hgy) ▸ hy
      · intro hmem
        exact ⟨x, hmem, rfl⟩
    by_cases hx : seen.contains x = true
    · rw [if_pos (by rw [hiff]; exact hx), if_pos hx]
      refine ih seen ?_
      intro u hu v hv huv
      exact hg
        (by
          rcases hu with hu | hu
          · exact Or.inl (List.mem_cons_of_mem _ hu)
          · exact Or.inr hu)
        (by
          rcases hv with hv | hv
          · exact Or.inl (List.mem_cons_of_mem _ hv)
          · exact Or.inr hv)
        huv
    · rw [if_neg (by rw [hiff]; exact hx), if_neg hx, List.map_cons]
      rw [show (g x :: seen.map g) = (x :: seen).map g from rfl]
      refine congrArg (g x :: ·) (ih (x :: seen) ?_)
      intro u hu v hv huv
      exact hg
        (by
          rcases hu with hu | hu
          · exact Or.inl (List.mem_cons_of_mem _ hu)
          · rcases List.mem_cons.mp hu with rfl | hu
            · exact Or.inl (by simp)
            · exact Or.inr hu)
        (by
          rcases hv with hv | hv
          · exact Or.inl (List.mem_cons_of_mem _ hv)
          · rcases List.mem_cons.mp hv with rfl | hv
            · exact Or.inl (by simp)
            · exact Or.inr hv)
        huv

/-- An injective renaming commutes with first-occurrence deduplication. -/
theorem distinctVarsAux_map_inj {g : VarName → VarName} (hg : Function.Injective g)
    (xs seen : List VarName) :
    distinctVarsAux (xs.map g) (seen.map g) = (distinctVarsAux xs seen).map g := by
  exact distinctVarsAux_map_injOn xs seen (fun _ _ _ _ h => hg h)

/-! ## §3  Canonical lookup gives the positional name; idxOf commutes with injective maps -/

/-- On a `Nodup` variable list, the canonical zip-index renaming sends a variable to its positional
    name `#α(idxOf)`. -/
theorem applyRen_canonList {ws : List VarName} (hnd : ws.Nodup)
    {v : VarName} (hv : v ∈ ws) :
    applyRen (ws.zipIdx.map (fun p => (p.1, "#α" ++ toString p.2))) v
      = "#α" ++ toString (ws.idxOf v) := by
  have hidx : ws.idxOf v < ws.length := List.idxOf_lt_length_of_mem hv
  have hfind :
      (ws.zipIdx.map (fun p => (p.1, "#α" ++ toString p.2))).find? (fun p => p.1 == v)
        = some (v, "#α" ++ toString (ws.idxOf v)) := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp, ws.idxOf v, by simp [hidx], ?_, ?_⟩
    · rw [List.getElem_map, List.getElem_zipIdx]; simp [List.getElem_idxOf hidx]
    · intro j hj
      have hjl : j < ws.length := by omega
      simp only [List.getElem_map, List.getElem_zipIdx, Bool.not_eq_true', beq_eq_false_iff_ne,
        ne_eq]
      intro hc
      have h2 : ws[j]'hjl = ws[ws.idxOf v]'hidx := by rw [hc, List.getElem_idxOf hidx]
      have := (List.Nodup.getElem_inj_iff hnd).mp h2
      omega
  unfold applyRen
  rw [hfind]
  simp

/-- Index-of commutes with an injective map. -/
theorem idxOf_map_injOn {g : VarName → VarName}
    (l : List VarName) (hg : Set.InjOn g {x | x ∈ l})
    {v : VarName} (hv : v ∈ l) :
    (l.map g).idxOf (g v) = l.idxOf v := by
  induction l generalizing v with
  | nil =>
      cases hv
  | cons x xs ih =>
      simp only [List.map_cons, List.idxOf_cons]
      by_cases hxv : x = v
      · subst hxv; simp
      · have hgxv : g x ≠ g v := by
          intro h
          apply hxv
          exact hg (by simp) (by simpa using hv) h
        have hvxs : v ∈ xs := (List.mem_cons.mp hv).resolve_left (fun h => hxv h.symm)
        have hgxs : Set.InjOn g {x | x ∈ xs} := by
          intro u hu w hw huw
          exact hg (List.mem_cons_of_mem _ hu) (List.mem_cons_of_mem _ hw) huw
        rw [show (g x == g v) = false from beq_eq_false_iff_ne.mpr hgxv,
            show (x == v) = false from beq_eq_false_iff_ne.mpr hxv]
        simp only [cond_false]
        simpa [Nat.succ_eq_add_one] using congrArg Nat.succ (ih hgxs hvxs)

/-- Index-of commutes with an injective map. -/
theorem idxOf_map_inj {g : VarName → VarName} (hg : Function.Injective g)
    (l : List VarName) (v : VarName) :
    (l.map g).idxOf (g v) = l.idxOf v := by
  by_cases hv : v ∈ l
  · exact idxOf_map_injOn l (fun _ _ _ _ h => hg h) hv
  · have hgv : g v ∉ l.map g := by
      intro hmem
      rcases List.mem_map.mp hmem with ⟨u, hu, huv⟩
      exact hv ((hg huv) ▸ hu)
    simp [hv, hgv]

/-! ## §4  CRUX 1 — canonicalize absorbs injective renaming -/

/-- **Keystone.** An injective renaming is inert under `canonicalizeVars`: the canonical form of a
    renamed atom is the canonical form of the original. Hence every freshening scheme (an injective
    renaming of rule variables) is invisible to the canonical core. -/
theorem canonicalizeVars_renBy_of_injOn_vars {g : VarName → VarName}
    {a : Atom} (hg : Set.InjOn g {v | v ∈ a.vars}) :
    canonicalizeVars (renBy g a) = canonicalizeVars a := by
  unfold canonicalizeVars
  rw [renBy_vars]
  have hdv :
      distinctVarsAux (a.vars.map g) []
        = (distinctVarsAux a.vars []).map g := by
    have hg0 : Set.InjOn g {v | v ∈ a.vars ∨ v ∈ ([] : List VarName)} := by
      intro u hu v hv huv
      exact hg
        (by
          rcases hu with hu | hu
          · exact hu
          · simp at hu)
        (by
          rcases hv with hv | hv
          · exact hv
          · simp at hv)
        huv
    have := distinctVarsAux_map_injOn a.vars [] hg0
    simpa using this
  rw [hdv, renameVars_eq_renBy, renameVars_eq_renBy, renBy_comp]
  refine renBy_congr ?_
  intro v hv
  set ws := distinctVarsAux a.vars [] with hws
  have hnd : ws.Nodup := distinctVarsAux_nodup a.vars []
  have hvws : v ∈ ws := by rw [hws, mem_distinctVarsAux]; exact ⟨hv, by simp⟩
  have hgvws : g v ∈ ws.map g := List.mem_map_of_mem hvws
  have hndg : (ws.map g).Nodup := by
    have : (distinctVarsAux (a.vars.map g) []).Nodup := distinctVarsAux_nodup (a.vars.map g) []
    simpa [hdv] using this
  have hL :
      applyRen ((ws.map g).zipIdx.map (fun p => (p.1, "#α" ++ toString p.2))) (g v)
        = "#α" ++ toString ((ws.map g).idxOf (g v)) := applyRen_canonList hndg hgvws
  have hR :
      applyRen (ws.zipIdx.map (fun p => (p.1, "#α" ++ toString p.2))) v
        = "#α" ++ toString (ws.idxOf v) := applyRen_canonList hnd hvws
  have hgws : Set.InjOn g {x | x ∈ ws} := by
    intro u hu w hw huw
    exact hg
      (by
        have hu' : u ∈ distinctVarsAux a.vars [] := by simpa [hws] using hu
        rw [mem_distinctVarsAux] at hu'
        exact hu'.1)
      (by
        have hw' : w ∈ distinctVarsAux a.vars [] := by simpa [hws] using hw
        rw [mem_distinctVarsAux] at hw'
        exact hw'.1)
      huw
  rw [hL, hR, idxOf_map_injOn ws hgws hvws]

/-- **Keystone.** An injective renaming is inert under `canonicalizeVars`: the canonical form of a
    renamed atom is the canonical form of the original. Hence every freshening scheme (an injective
    renaming of rule variables) is invisible to the canonical core. -/
theorem canonicalizeVars_renBy_of_injective {g : VarName → VarName}
    (hg : Function.Injective g) (a : Atom) :
    canonicalizeVars (renBy g a) = canonicalizeVars a := by
  exact canonicalizeVars_renBy_of_injOn_vars (a := a) (fun _ _ _ _ h => hg h)

/-! ## §5  CRUX 1 for the list-renamer -/

/-- `Metta.renameVars m` is inert under `canonicalizeVars` when its induced leaf map is injective on
    the variables that actually occur in the atom. -/
theorem canonicalizeVars_renameVars_of_injOn_vars {m : List (VarName × VarName)}
    {a : Atom} (hinj : Set.InjOn (applyRen m) {v | v ∈ a.vars}) :
    canonicalizeVars (Metta.renameVars m a) = canonicalizeVars a := by
  rw [renameVars_eq_renBy]
  exact canonicalizeVars_renBy_of_injOn_vars (a := a) hinj

/-- `Metta.renameVars m` is inert under `canonicalizeVars` when its induced leaf map is injective. -/
theorem canonicalizeVars_renameVars_of_injective {m : List (VarName × VarName)}
    (hinj : Function.Injective (applyRen m)) (a : Atom) :
    canonicalizeVars (Metta.renameVars m a) = canonicalizeVars a := by
  exact canonicalizeVars_renameVars_of_injOn_vars (a := a) (fun _ _ _ _ h => hinj h)

end Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
