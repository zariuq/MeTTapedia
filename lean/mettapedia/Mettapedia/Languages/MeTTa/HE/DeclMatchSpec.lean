import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.HE.Matching
import Mettapedia.Languages.MeTTa.HE.BindingComposition

/-!
# Declarative HE match specification (Phase 1b/1c)

The **declarative** spec for HE atom matching: `MatchRel l r b` holds iff binding set `b` is a valid
match of `l` against `r`, **faithful to the author's English spec** `match_atoms`
(`Specs/he_metta_official_specs.md:397-435`). This is the relation the computable `matchAtoms`
(`Matching.lean`) is to be proven sound + complete against (Phase 2, the mm-lean4 discipline), and the
spec the equation-query path must use instead of the simplified `simpleMatch`.

## Provenance discipline (anti-circularity)
Every constructor cites an English-spec line `[:NNN]`. The relation is anchored to the **author's text**,
not to LeaTTa or to the previous LLM-drafted Lean. (See `Specs/he_metta_official_specs.ai_draft_v0.md`.)

## Phase 1b design decision — dedicated HE binding relation, NOT OSLF `Pattern`
OSLF's binding model is value-only (`OSLF/MeTTaIL/Match.lean`: `Bindings := List (String × Pattern)`;
`matchPattern`'s var case `.fvar x, t => [[(x,t)]]` — so var/var yields an *oriented value binding*, the
same simplification as `simpleMatch`, **not** the equality `$x=$y`). OSLF is the binder/de-Bruijn layer
(Layer B). HE's metavariable/equation matching (Layer M) needs the **two-relation** model (value `<-`
*and* equality `=`), so the declarative spec uses a **dedicated HE relation** built on the faithful
`matchAtoms`/`mergeBindings`; OSLF is reserved for the binder layer.

## The keystone (1c)
`matchRel_varVar_inv` + the var/var negative witness make the bug **undeniable**: the output of the
simplified `simpleMatch` on two variables (an oriented assignment `$x <- $y`) is **provably not** a valid
match under the faithful spec (which requires the equality `$x = $y`). This is exactly the divergence the
Phase-2 faithfulness theorem will catch, and why the equation-query path must move to `matchAtoms`.
-/

namespace Mettapedia.Languages.MeTTa.HE.DeclMatchSpec

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Is the atom a variable leaf? (guard for the one-variable match cases). -/
def Atom.isVarB : Atom → Bool
  | .var _ => true
  | _ => false

/-! ## §1  The declarative match relation (faithful to `match_atoms`, `:397-435`)

Binding sets are written as literals `⟨assignments, equalities⟩` (definitionally equal to
`Bindings.empty`/`.assign`/`.addEquality`) so dependent elimination sees their structure.

Important: the expression case is stated in the **same left-to-right accumulator-threading shape**
as `matchAtomsList` and the English algorithm ("match pointwise, threading merge after each
position", `:418-425`). This keeps the declarative relation aligned with the executable matcher
instead of smuggling in a different association shape for merge. -/

mutual

/-- `MatchRel l r b` : `b` witnesses a match of `l` against `r`. -/
inductive MatchRel : Atom → Atom → Bindings → Prop where
  /-- Identical symbols match with empty bindings. `[:410]` -/
  | symSym (s : String) : MatchRel (.symbol s) (.symbol s) ⟨[], []⟩
  /-- Two variables produce an **equality** relation `$a = $b` (NOT an oriented assignment). `[:412]` -/
  | varVar (a b : String) : MatchRel (.var a) (.var b) ⟨[], [(a, b)]⟩
  /-- A variable against a non-variable assigns the non-variable to it. `[:414]` -/
  | varNonVar {v : String} {t : Atom} :
      Atom.isVarB t = false → MatchRel (.var v) t ⟨[(v, t)], []⟩
  /-- A non-variable against a variable assigns to the **right** variable (two-sided). `[:416]` -/
  | nonVarVar {s : Atom} {v : String} :
      Atom.isVarB s = false → MatchRel s (.var v) ⟨[(v, s)], []⟩
  /-- Grounded atoms: structural equality (implementation behavior; the published `[{}]` fallback at
      `:430-431` is unreachable because grounded atoms carry custom matchers — see `Matching.lean`). -/
  | grounded (g : GroundedValue) : MatchRel (.grounded g) (.grounded g) ⟨[], []⟩
  /-- Expressions match pointwise with merge threaded after each position. `[:418-425]` -/
  | expr {ls rs : List Atom} {b : Bindings} :
      MatchListAccRel ls rs Bindings.empty b →
      MatchRel (.expression ls) (.expression rs) b

/-- Accumulator-threaded list match relation, mirroring `matchAtomsList`.
    The accumulator is the current merged binding set produced by the already-matched prefix.
    `[:418-425, :436-492]` -/
inductive MatchListAccRel : List Atom → List Atom → Bindings → Bindings → Prop where
  | nil {seed : Bindings} : MatchListAccRel [] [] seed seed
  | cons {l r : Atom} {ls rs : List Atom}
      {seed bH bNext bOut : Bindings} {fuel : Nat} :
      MatchRel l r bH →
      bNext ∈ mergeBindings seed bH fuel →
      MatchListAccRel ls rs bNext bOut →
      MatchListAccRel (l :: ls) (r :: rs) seed bOut

end

/-- Public list-match view: start from empty bindings, exactly like `matchAtoms` on expressions. -/
abbrev MatchListRel (ls rs : List Atom) (b : Bindings) : Prop :=
  MatchListAccRel ls rs Bindings.empty b

/-! ## §2  Inversion lemmas (the binding index is free → no string-unification trap) -/

/-- Matching two variables forces the **equality** binding — there is no other derivation. `[:412]` -/
theorem matchRel_varVar_inv {a b : String} {bb : Bindings}
    (h : MatchRel (.var a) (.var b) bb) : bb = ⟨[], [(a, b)]⟩ := by
  cases h with
  | varVar => rfl
  | varNonVar hnv => simp [Atom.isVarB] at hnv
  | nonVarVar hnv => simp [Atom.isVarB] at hnv

/-- Matching two symbols forces them equal, with empty bindings. `[:410]` -/
theorem matchRel_symSym_inv {a c : String} {bb : Bindings}
    (h : MatchRel (.symbol a) (.symbol c) bb) : a = c ∧ bb = ⟨[], []⟩ := by
  cases h with
  | symSym => exact ⟨rfl, rfl⟩

/-! ## §3  Positive witnesses (1c) — spec-compliant matches -/

example : MatchRel (.symbol "f") (.symbol "f") Bindings.empty := .symSym "f"
/-- var/var ⇒ equality `$x = $y`. -/
example : MatchRel (.var "x") (.var "y") (Bindings.empty.addEquality "x" "y") := .varVar "x" "y"
example : MatchRel (.var "x") (.symbol "a") (Bindings.empty.assign "x" (.symbol "a")) := .varNonVar rfl
example : MatchRel (.symbol "a") (.var "x") (Bindings.empty.assign "x" (.symbol "a")) := .nonVarVar rfl
example (g : GroundedValue) : MatchRel (.grounded g) (.grounded g) Bindings.empty := .grounded g

/-! ## §4  Negative witnesses (1c) — non-matches the faithful spec rejects

The first is the **keystone**: the simplified `simpleMatch` produces an oriented assignment for var/var
(`Space.lean:161`, `b.assign v target`); that output is provably **not** a valid match here, because the
faithful spec requires the equality relation. This is the divergence the equation-query path must fix. -/

/-- KEYSTONE: var/var oriented-assignment (what `simpleMatch` emits) is NOT a faithful match. -/
example : ¬ MatchRel (.var "x") (.var "y") (Bindings.empty.assign "x" (.var "y")) := by
  intro h
  have hb := matchRel_varVar_inv h
  simp [Bindings.empty, Bindings.assign] at hb

/-- Different symbols do not match under any binding. `[:410]` -/
example {bb : Bindings} : ¬ MatchRel (.symbol "f") (.symbol "g") bb := by
  intro h
  have := (matchRel_symSym_inv h).1
  simp at this

/-! ## §5  Operational matcher soundness

The executable `matchAtoms`/`matchAtomsList` only produce declaratively valid HE matches.
This is the mm-lean4-style "operational implies declarative" half of the equivalence. -/

/-- Fuel-indexed paired soundness statement for `matchAtoms` and `matchAtomsList`.
    Packaging them together avoids a spurious mutual-termination fight while keeping the
    actual semantic dependency explicit: both use the predecessor fuel. -/
private theorem matchSoundPair :
    ∀ fuel,
      (∀ {l r : Atom} {b : Bindings},
          b ∈ matchAtoms l r fuel → MatchRel l r b) ∧
      (∀ {ls rs : List Atom} {acc : List Bindings} {b : Bindings},
          b ∈ matchAtomsList ls rs acc fuel →
            ∃ seed, seed ∈ acc ∧ MatchListAccRel ls rs seed b)
  | 0 => by
      constructor
      · intro l r b h
        simp [matchAtoms] at h
      · intro ls rs acc b h
        simp [matchAtomsList] at h
  | fuel + 1 => by
      rcases matchSoundPair fuel with ⟨ihAtoms, ihLists⟩
      constructor
      · intro l r b h
        cases l with
        | symbol s =>
            cases r with
            | symbol t =>
                by_cases hst : s = t
                · subst hst
                  simp [matchAtoms, getMetaType, Atom.symbolType] at h
                  have hb : b = Bindings.empty := by
                    simpa using h.1
                  subst b
                  exact .symSym s
                · simp [matchAtoms, getMetaType, Atom.symbolType, hst] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.variableType] at h
                have hb : b = Bindings.empty.assign v (.symbol s) := by
                  simpa using h.1
                subst b
                exact .nonVarVar rfl
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at h
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at h
        | var v =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.variableType] at h
                have hb : b = Bindings.empty.assign v (.symbol s) := by
                  simpa using h.1
                subst b
                exact .varNonVar rfl
            | var w =>
                simp [matchAtoms, getMetaType, Atom.variableType] at h
                have hb : b = Bindings.empty.addEquality v w := by
                  simpa using h.1
                subst b
                exact .varVar v w
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.variableType, Atom.groundedType] at h
                have hb : b = Bindings.empty.assign v (.grounded g) := by
                  simpa using h.1
                subst b
                exact .varNonVar rfl
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.variableType, Atom.expressionType] at h
                have hb : b = Bindings.empty.assign v (.expression es) := by
                  simpa using h.1
                subst b
                exact .varNonVar rfl
        | grounded g =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.variableType, Atom.groundedType] at h
                have hb : b = Bindings.empty.assign v (.grounded g) := by
                  simpa using h.1
                subst b
                exact .nonVarVar rfl
            | grounded hG =>
                by_cases hg : g = hG
                · subst hg
                  simp [matchAtoms, getMetaType, Atom.groundedType] at h
                  have hb : b = Bindings.empty := by
                    simpa using h.1
                  subst b
                  exact .grounded g
                · simp [matchAtoms, getMetaType, Atom.groundedType, hg] at h
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at h
        | expression ls =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.variableType, Atom.expressionType] at h
                have hb : b = Bindings.empty.assign v (.expression ls) := by
                  simpa using h.1
                subst b
                exact .nonVarVar rfl
            | grounded g =>
                simp [matchAtoms, getMetaType] at h
            | expression rs =>
                by_cases hlen : ls.length = rs.length
                · simp [matchAtoms, getMetaType, Atom.expressionType, hlen] at h
                  rcases h with ⟨hList, _⟩
                  rcases ihLists hList with ⟨seed, hseed, hrel⟩
                  simp at hseed
                  subst seed
                  exact .expr hrel
                · simp [matchAtoms, getMetaType, Atom.expressionType, hlen] at h
      · intro ls rs acc b h
        cases ls <;> cases rs <;> simp [matchAtomsList] at h
        case nil.nil =>
          exact ⟨b, h, .nil⟩
        case cons.cons l ls r rs =>
          rcases ihLists h with ⟨seed, hseed, hrel⟩
          rcases List.mem_flatMap.mp hseed with ⟨accSeed, hacc, hseed'⟩
          rcases List.mem_flatMap.mp hseed' with ⟨bHead, hhead, hmerge⟩
          have hHeadRel : MatchRel l r bHead := ihAtoms hhead
          exact ⟨accSeed, hacc, .cons hHeadRel hmerge hrel⟩

/-- Soundness of the executable matcher against the faithful declarative relation. -/
theorem matchAtoms_sound {l r : Atom} {b : Bindings} {fuel : Nat}
    (h : b ∈ matchAtoms l r fuel) : MatchRel l r b :=
  (matchSoundPair fuel).1 h

/-- Generalized soundness for `matchAtomsList`: any returned binding comes from some seed in the
    accumulator threaded through declaratively valid pointwise matches. -/
theorem matchAtomsList_sound {ls rs : List Atom} {acc : List Bindings}
    {b : Bindings} {fuel : Nat}
    (h : b ∈ matchAtomsList ls rs acc fuel) :
    ∃ seed, seed ∈ acc ∧ MatchListAccRel ls rs seed b :=
  (matchSoundPair fuel).2 h

/-! ## §6  Fuel monotonicity and seeded reassembly

Completeness for the expression/list fragment has one real technical crux:
`MatchListAccRel` stores successful `mergeBindings` steps with their own local
fuel witnesses, but `matchAtomsList` executes the whole threaded run at a
single common fuel.  The following private toolkit is the local, declarative-file
copy of the exact fuel-monotonicity / seedwise-decomposition facts needed to
reassemble those local witnesses into one official run.

We intentionally keep this machinery here instead of importing the broader
bridge layer: the matcher equivalence is foundational and should not depend on
later cross-runtime files. -/

/-- Pointwise list inclusion on binding lists. -/
private def BSub (xs ys : List Bindings) : Prop := ∀ x ∈ xs, x ∈ ys

private theorem BSub.refl (xs : List Bindings) : BSub xs xs := fun _ h => h

/-- `matchAtomsList` distributes over a `flatMap`-built accumulator. -/
private theorem matchAtomsList_flatMap_acc
    {α : Type} (lefts rights : List Atom) (acc : List α)
    (f : α → List Bindings) (fuel : Nat) :
    matchAtomsList lefts rights (acc.flatMap f) fuel =
      acc.flatMap (fun a => matchAtomsList lefts rights (f a) fuel) := by
  induction fuel generalizing lefts rights acc f with
  | zero =>
      simp [matchAtomsList]
  | succ n ih =>
      cases lefts with
      | nil =>
          cases rights with
          | nil =>
              simp [matchAtomsList]
          | cons right rights =>
              simp [matchAtomsList]
      | cons left lefts =>
          cases rights with
          | nil =>
              simp [matchAtomsList]
          | cons right rights =>
              simp only [matchAtomsList]
              rw [List.flatMap_assoc]
              simpa using
                ih lefts rights acc
                  (fun a =>
                    (f a).flatMap fun b =>
                      (matchAtoms left right n).flatMap fun mb =>
                        mergeBindings b mb n)

/-- `matchAtomsList` decomposes seedwise over its accumulator. -/
private theorem matchAtomsList_seedwise
    (lefts rights : List Atom) (seeds : List Bindings) (fuel : Nat) :
    matchAtomsList lefts rights seeds fuel =
      seeds.flatMap (fun b => matchAtomsList lefts rights [b] fuel) := by
  simpa using
    (matchAtomsList_flatMap_acc lefts rights seeds (fun b => [b]) fuel)

private theorem flatMap_bsub {xs xs' : List Bindings}
    {f g : Bindings → List Bindings}
    (h_xs : BSub xs xs') (h_fg : ∀ a ∈ xs, BSub (f a) (g a)) :
    BSub (xs.flatMap f) (xs'.flatMap g) := by
  intro x hx
  obtain ⟨a, ha, hfa⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨a, h_xs a ha, h_fg a ha x hfa⟩

private theorem foldl_flatMap_bsub {α : Type} (l : List α)
    {step step' : List Bindings → α → List Bindings}
    (h_step : ∀ acc acc' a, BSub acc acc' → BSub (step acc a) (step' acc' a)) :
    ∀ {acc acc' : List Bindings}, BSub acc acc' →
      BSub (l.foldl step acc) (l.foldl step' acc') := by
  induction l with
  | nil =>
      intro acc acc' h
      simpa using h
  | cons a as ih =>
      intro acc acc' h
      simp only [List.foldl_cons]
      exact ih (h_step acc acc' a h)

/-- Simultaneous fuel-monotonicity for the matcher family. -/
private theorem matcher_mono_local : ∀ n : Nat,
    (∀ l r, BSub (matchAtoms l r n) (matchAtoms l r (n + 1))) ∧
    (∀ ls rs acc acc', BSub acc acc' →
      BSub (matchAtomsList ls rs acc n) (matchAtomsList ls rs acc' (n + 1))) ∧
    (∀ a b, BSub (mergeBindings a b n) (mergeBindings a b (n + 1))) ∧
    (∀ b v val, BSub (addVarBinding b v val n) (addVarBinding b v val (n + 1))) ∧
    (∀ b a c, BSub (addVarEquality b a c n) (addVarEquality b a c (n + 1))) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        first
          | (intro l r x hx; simp [matchAtoms] at hx)
          | (intro ls rs acc acc' h x hx; simp [matchAtomsList] at hx)
          | (intro a b x hx; simp [mergeBindings] at hx)
          | (intro b v val x hx; simp [addVarBinding] at hx)
          | (intro b a c x hx; simp [addVarEquality] at hx)
  | succ n ih =>
      obtain ⟨ihA, ihL, ihM, ihB, ihE⟩ := ih
      have hsubRefl : ∀ xs : List Bindings, BSub xs xs := BSub.refl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro l r x hx
        simp only [matchAtoms, List.mem_filter, beq_iff_eq, Bool.and_eq_true] at hx ⊢
        refine ⟨?_, hx.2⟩
        have hx1 := hx.1
        repeat'
          first
            | exact hx1
            | exact absurd ‹_› ‹_›
            | (split at hx1 <;> split <;>
                first
                  | exact hx1
                  | exact absurd ‹_› ‹_›
                  | skip)
        all_goals
          first
            | contradiction
            | (split at hx1
               · split at hx1
                 · rename_i hlen
                   rw [if_pos hlen]
                   exact ihL _ _ _ _ (hsubRefl _) x hx1
                 · rename_i hlen
                   rw [if_neg hlen]
                   exact hx1
               · exact hx1)
      · intro ls rs acc acc' hacc x hx
        simp only [matchAtomsList] at hx ⊢
        split at hx
        · exact hacc x hx
        · rename_i l1 ls1 r1 rs1
          exact ihL _ _ _ _
            (flatMap_bsub hacc
              (fun a _ => flatMap_bsub (ihA l1 r1) (fun bnd _ => ihM a bnd)))
            x hx
        · exact absurd hx (by simp)
      · intro a b x hx
        simp only [mergeBindings] at hx ⊢
        refine foldl_flatMap_bsub b.equalities
          (fun acc acc' p h => flatMap_bsub h (fun bd _ => ihE bd p.1 p.2)) ?_ x hx
        exact foldl_flatMap_bsub b.assignments
          (fun acc acc' p h => flatMap_bsub h (fun bd _ => ihB bd p.1 p.2))
          (hsubRefl [a])
      · intro b v val x hx
        cases hlook : b.lookup v with
        | none =>
            simp only [addVarBinding, hlook] at hx ⊢
            exact hx
        | some prev =>
            simp only [addVarBinding, hlook] at hx ⊢
            split at hx <;> rename_i heq
            · rw [if_pos heq]
              exact hx
            · rw [if_neg heq]
              exact flatMap_bsub (ihA _ _) (fun mb _ => ihM b mb) x hx
      · intro b a c x hx
        cases hA : b.lookup a with
        | none =>
            simp only [addVarEquality, hA] at hx ⊢
            exact hx
        | some av =>
            cases hC : b.lookup c with
            | none =>
                simp only [addVarEquality, hA, hC] at hx ⊢
                exact hx
            | some cv =>
                simp only [addVarEquality, hA, hC] at hx ⊢
                split at hx <;> rename_i heq
                · rw [if_pos heq]
                  exact hx
                · rw [if_neg heq]
                  exact flatMap_bsub (ihA _ _) (fun mb _ => ihM b mb) x hx

private theorem matchAtoms_mono_add
    (l r : Atom) (fuel extra : Nat) :
    BSub (matchAtoms l r fuel) (matchAtoms l r (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using BSub.refl (matchAtoms l r fuel)
  | succ extra ih =>
      have hstep := (matcher_mono_local (fuel + extra)).1 l r
      exact fun x hx => hstep x (ih x hx)

private theorem matchAtomsList_mono_add
    (ls rs : List Atom) (acc : List Bindings) (fuel extra : Nat) :
    BSub (matchAtomsList ls rs acc fuel) (matchAtomsList ls rs acc (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using BSub.refl (matchAtomsList ls rs acc fuel)
  | succ extra ih =>
      have hstep := (matcher_mono_local (fuel + extra)).2.1 ls rs acc acc (BSub.refl _)
      exact fun x hx => hstep x (ih x hx)

private theorem mergeBindings_mono_add
    (left right : Bindings) (fuel extra : Nat) :
    BSub (mergeBindings left right fuel) (mergeBindings left right (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using BSub.refl (mergeBindings left right fuel)
  | succ extra ih =>
      have hstep := (matcher_mono_local (fuel + extra)).2.2.1 left right
      exact fun x hx => hstep x (ih x hx)

/-- Promote separate head-match and merge witnesses to one flatMap-style head step
    at a common fuel. -/
private theorem matchAtoms_head_step_of_match_merge
    {l r : Atom} {seed bH bNext : Bindings} {fuelMatch fuelMerge : Nat}
    (hmatch : bH ∈ matchAtoms l r fuelMatch)
    (hmerge : bNext ∈ mergeBindings seed bH fuelMerge) :
    ∃ fuel,
      bNext ∈ (matchAtoms l r fuel).flatMap (fun mb => mergeBindings seed mb fuel) := by
  let fuel := max fuelMatch fuelMerge
  have hMatchLe : fuelMatch ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_left _ _
  have hMergeLe : fuelMerge ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_right _ _
  have hMatchEq : fuelMatch + (fuel - fuelMatch) = fuel :=
    Nat.add_sub_of_le hMatchLe
  have hMergeEq : fuelMerge + (fuel - fuelMerge) = fuel :=
    Nat.add_sub_of_le hMergeLe
  have hmatch' : bH ∈ matchAtoms l r fuel := by
    simpa [hMatchEq] using
      (matchAtoms_mono_add l r fuelMatch (fuel - fuelMatch)) bH hmatch
  have hmerge' : bNext ∈ mergeBindings seed bH fuel := by
    simpa [hMergeEq] using
      (mergeBindings_mono_add seed bH fuelMerge (fuel - fuelMerge)) bNext hmerge
  exact ⟨fuel, List.mem_flatMap.mpr ⟨bH, hmatch', hmerge'⟩⟩

/-- Reassemble a successful head step and a successful singleton-seeded tail run
    into one official `matchAtomsList` run from the original singleton seed. -/
private theorem matchAtomsList_cons_of_head_tail
    {t p : Atom} {ts ps : List Atom}
    {b b' qb : Bindings} {fuelHead fuelTail : Nat}
    (hhead :
      b' ∈ (matchAtoms t p fuelHead).flatMap (fun mb => mergeBindings b mb fuelHead))
    (htail : qb ∈ matchAtomsList ts ps [b'] fuelTail) :
    ∃ fuel, qb ∈ matchAtomsList (t :: ts) (p :: ps) [b] fuel := by
  let fuel := max fuelHead fuelTail
  have hHeadLe : fuelHead ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_left _ _
  have hTailLe : fuelTail ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_right _ _
  have hHeadEq : fuelHead + (fuel - fuelHead) = fuel :=
    Nat.add_sub_of_le hHeadLe
  have hTailEq : fuelTail + (fuel - fuelTail) = fuel :=
    Nat.add_sub_of_le hTailLe
  have hhead' :
      b' ∈ (matchAtoms t p fuel).flatMap (fun mb => mergeBindings b mb fuel) := by
    refine (flatMap_bsub ?_ ?_) _ hhead
    · simpa [hHeadEq] using
        (matchAtoms_mono_add t p fuelHead (fuel - fuelHead))
    · intro mb hmb
      simpa [hHeadEq] using
        (mergeBindings_mono_add b mb fuelHead (fuel - fuelHead))
  have htail' : qb ∈ matchAtomsList ts ps [b'] fuel := by
    simpa [hTailEq] using
      (matchAtomsList_mono_add ts ps [b'] fuelTail (fuel - fuelTail)) qb htail
  have hseeded :
      qb ∈ matchAtomsList ts ps
        ((matchAtoms t p fuel).flatMap fun mb => mergeBindings b mb fuel) fuel := by
    rw [matchAtomsList_seedwise ts ps
      ((matchAtoms t p fuel).flatMap fun mb => mergeBindings b mb fuel) fuel]
    exact List.mem_flatMap.mpr ⟨b', hhead', htail'⟩
  refine ⟨fuel + 1, ?_⟩
  simpa [matchAtomsList] using hseeded

/-! ## §7  No-variable-values implies no loop

This isolates the semantic shape of the remaining completeness crux.  The top
level `matchAtoms` surface filters out looped bindings, so any future
`MatchRel -> hasLoop = false` theorem will naturally factor through the more
structural statement that successful bindings never map a variable directly to
another variable. -/

/-- Strong structural invariant: every assigned value in the binding list is
    visibly non-variable. This is easier to preserve through the executable
    folds than the lookup-based `NoVarAssignmentValues` boundary, and it
    implies that boundary immediately. -/
private def AssignmentValuesNonVar (b : Bindings) : Prop :=
  ∀ ⦃v a⦄, (v, a) ∈ b.assignments → Atom.isVarB a = false

private theorem AssignmentValuesNonVar.empty :
    AssignmentValuesNonVar Bindings.empty := by
  intro v a hmem
  cases hmem

private theorem AssignmentValuesNonVar.assign_of_lookup_none
    {b : Bindings} (hvals : AssignmentValuesNonVar b)
    {v : String} {val : Atom} (hnone : b.lookup v = none)
    (hval : Atom.isVarB val = false) :
    AssignmentValuesNonVar (b.assign v val) := by
  intro w a hmem
  have hnotbound : b.isBound v = false :=
    isBound_false_of_lookup_none hnone
  unfold Bindings.assign at hmem
  simp [hnotbound] at hmem
  rcases hmem with hmem | hmem
  · exact hvals hmem
  · rcases hmem with ⟨rfl, rfl⟩
    exact hval

private theorem AssignmentValuesNonVar.removeAssignment
    {b : Bindings} (hvals : AssignmentValuesNonVar b) (v : String) :
    AssignmentValuesNonVar (b.removeAssignment v) := by
  intro w a hmem
  unfold Bindings.removeAssignment at hmem
  simp at hmem
  exact hvals hmem.1

private theorem AssignmentValuesNonVar.addEquality
    {b : Bindings} (hvals : AssignmentValuesNonVar b) (a c : String) :
    AssignmentValuesNonVar (b.addEquality a c) := hvals

private theorem assignmentValuesNonVar_of_singleton_assign
    {v : String} {val : Atom} (hval : Atom.isVarB val = false) :
    AssignmentValuesNonVar (Bindings.empty.assign v val) := by
  exact
    AssignmentValuesNonVar.assign_of_lookup_none
      AssignmentValuesNonVar.empty rfl hval

/-- Boundary predicate: no HE lookup returns a bare variable payload. -/
private def NoVarAssignmentValues (b : Bindings) : Prop :=
  ∀ ⦃v x⦄, b.lookup v = some (.var x) → False

private theorem lookup_some_mem_assignments {xs : List (String × Atom)}
    {v : String} {a : Atom} (h : List.lookup v xs = some a) :
    (v, a) ∈ xs := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      by_cases hk : v == k
      · have hvk : v = k := by
          simpa using hk
        simp [List.lookup_cons, hk] at h
        subst hvk
        subst h
        simp
      · simp [List.lookup_cons, hk] at h
        simpa using Or.inr (ih h)

private theorem lookup_some_of_mem_assignment {xs : List (String × Atom)}
    {v : String} {a : Atom} (hmem : (v, a) ∈ xs) :
    ∃ a', List.lookup v xs = some a' := by
  induction xs with
  | nil =>
      cases hmem
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      simp at hmem
      rcases hmem with h | h
      · rcases h with ⟨rfl, rfl⟩
        refine ⟨a, ?_⟩
        simp
      · by_cases hk : v == k
        · exact ⟨b, by simp [List.lookup_cons, hk]⟩
        · rcases ih h with ⟨a', ha'⟩
          exact ⟨a', by simp [List.lookup_cons, hk, ha']⟩

private theorem AssignmentValuesNonVar.noVar {b : Bindings}
    (hvals : AssignmentValuesNonVar b) :
    NoVarAssignmentValues b := by
  intro v x hlookup
  have hmem : (v, .var x) ∈ b.assignments :=
    lookup_some_mem_assignments hlookup
  simpa [Atom.isVarB] using hvals hmem

/-- Structural non-variable-valuedness is preserved by the executable HE
    matcher family. This is the real semantic invariant behind later
    loop-freedom: successful matcher/merge outputs never introduce a direct
    variable-to-variable assignment. -/
private theorem matcherAssignmentsNonVar :
    ∀ fuel,
      (∀ {l r : Atom} {b : Bindings},
          b ∈ matchAtoms l r fuel →
            AssignmentValuesNonVar b) ∧
      (∀ {ls rs : List Atom} {acc : List Bindings} {b : Bindings},
          b ∈ matchAtomsList ls rs acc fuel →
            (∀ seed ∈ acc, AssignmentValuesNonVar seed) →
            AssignmentValuesNonVar b) ∧
      (∀ {left right out : Bindings},
          out ∈ mergeBindings left right fuel →
            AssignmentValuesNonVar left →
            AssignmentValuesNonVar right →
            AssignmentValuesNonVar out) ∧
      (∀ {b : Bindings} {v : String} {val : Atom} {out : Bindings},
          out ∈ addVarBinding b v val fuel →
            AssignmentValuesNonVar b →
            Atom.isVarB val = false →
            AssignmentValuesNonVar out) ∧
      (∀ {b : Bindings} {a c : String} {out : Bindings},
          out ∈ addVarEquality b a c fuel →
            AssignmentValuesNonVar b →
            AssignmentValuesNonVar out) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro l r b h
        simp [matchAtoms] at h
      · intro ls rs acc b h
        simp [matchAtomsList] at h
      · intro left right out h
        simp [mergeBindings] at h
      · intro b v val out h
        simp [addVarBinding] at h
      · intro b a c out h
        simp [addVarEquality] at h
  | succ n ih =>
      obtain ⟨ihAtoms, ihLists, ihMerge, ihBind, ihEq⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro l r b h
        cases l with
        | symbol s =>
            cases r with
            | symbol t =>
                by_cases hst : s = t
                · subst hst
                  simp [matchAtoms, getMetaType, Atom.symbolType] at h
                  have hb : b = Bindings.empty := by
                    simpa using h.1
                  subst hb
                  exact AssignmentValuesNonVar.empty
                · simp [matchAtoms, getMetaType, Atom.symbolType, hst] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.variableType] at h
                have hb : b = Bindings.empty.assign v (.symbol s) := by
                  simpa using h.1
                subst hb
                exact assignmentValuesNonVar_of_singleton_assign rfl
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at h
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at h
        | var v =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.variableType] at h
                have hb : b = Bindings.empty.assign v (.symbol s) := by
                  simpa using h.1
                subst hb
                exact assignmentValuesNonVar_of_singleton_assign rfl
            | var w =>
                simp [matchAtoms, getMetaType, Atom.variableType] at h
                have hb : b = Bindings.empty.addEquality v w := by
                  simpa using h.1
                subst hb
                exact AssignmentValuesNonVar.empty
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.variableType, Atom.groundedType] at h
                have hb : b = Bindings.empty.assign v (.grounded g) := by
                  simpa using h.1
                subst hb
                exact assignmentValuesNonVar_of_singleton_assign rfl
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.variableType, Atom.expressionType] at h
                have hb : b = Bindings.empty.assign v (.expression es) := by
                  simpa using h.1
                subst hb
                exact assignmentValuesNonVar_of_singleton_assign rfl
        | grounded g =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.variableType, Atom.groundedType] at h
                have hb : b = Bindings.empty.assign v (.grounded g) := by
                  simpa using h.1
                subst hb
                exact assignmentValuesNonVar_of_singleton_assign rfl
            | grounded g' =>
                by_cases hgg : g = g'
                · subst hgg
                  simp [matchAtoms, getMetaType, Atom.groundedType] at h
                  have hb : b = Bindings.empty := by
                    simpa using h.1
                  subst hb
                  exact AssignmentValuesNonVar.empty
                · simp [matchAtoms, getMetaType, Atom.groundedType, hgg] at h
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at h
        | expression ls =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.variableType, Atom.expressionType] at h
                have hb : b = Bindings.empty.assign v (.expression ls) := by
                  simpa using h.1
                subst hb
                exact assignmentValuesNonVar_of_singleton_assign rfl
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at h
            | expression rs =>
                by_cases hlen : ls.length = rs.length
                · simp [matchAtoms, getMetaType, Atom.expressionType, hlen] at h
                  rcases h with ⟨hList, _⟩
                  exact ihLists hList (by
                    intro seed hseed
                    simp at hseed
                    subst seed
                    exact AssignmentValuesNonVar.empty)
                · simp [matchAtoms, getMetaType, Atom.expressionType, hlen] at h
      · intro ls rs acc b h hacc
        cases ls with
        | nil =>
            cases rs with
            | nil =>
                simp [matchAtomsList] at h
                exact hacc _ h
            | cons r rs =>
                simp [matchAtomsList] at h
        | cons l ls =>
            cases rs with
            | nil =>
                simp [matchAtomsList] at h
            | cons r rs =>
                simp [matchAtomsList] at h
                have hnext :
                    ∀ seed ∈
                      acc.flatMap
                        (fun a =>
                          (matchAtoms l r n).flatMap
                            (fun mb => mergeBindings a mb n)),
                      AssignmentValuesNonVar seed := by
                  intro seed hseed
                  rcases List.mem_flatMap.mp hseed with ⟨a, ha, hseed⟩
                  rcases List.mem_flatMap.mp hseed with ⟨mb, hmb, hmerge⟩
                  exact ihMerge hmerge (hacc a ha) (ihAtoms hmb)
                exact ihLists h hnext
      · intro left right out h hleft hright
        simp only [mergeBindings] at h
        have hAssignFold :
            ∀ (assigns : List (String × Atom)) {acc out},
              out ∈ List.foldl
                (fun (acc : List Bindings) (v, val) =>
                  List.flatMap (fun b => addVarBinding b v val n) acc) acc assigns →
              (∀ b ∈ acc, AssignmentValuesNonVar b) →
              (∀ (p : String × Atom), p ∈ assigns → Atom.isVarB p.2 = false) →
              AssignmentValuesNonVar out := by
          intro assigns
          induction assigns with
          | nil =>
              intro acc out hout hacc hvals
              exact hacc out hout
          | cons p ps ihPs =>
              intro acc out hout hacc hvals
              rcases p with ⟨v, val⟩
              simp only [List.foldl_cons] at hout
              have hnext :
                  ∀ b ∈ acc.flatMap (fun bd => addVarBinding bd v val n),
                    AssignmentValuesNonVar b := by
                intro b hb
                rcases List.mem_flatMap.mp hb with ⟨seed, hseed, hadd⟩
                exact ihBind hadd (hacc seed hseed) (hvals (v, val) (by simp))
              have hvalsTail :
                  ∀ p ∈ ps, Atom.isVarB p.2 = false := by
                intro p hp
                exact hvals p (by simp [hp])
              exact ihPs hout hnext hvalsTail
        have hEqFold :
            ∀ (eqs : List (String × String)) {acc : List Bindings} {out : Bindings},
              out ∈ List.foldl
                (fun (acc : List Bindings) (a, c) =>
                  List.flatMap (fun bd => addVarEquality bd a c n) acc) acc eqs →
              (∀ b ∈ acc, AssignmentValuesNonVar b) →
              AssignmentValuesNonVar out := by
          intro eqs
          induction eqs with
          | nil =>
              intro acc out hout hacc
              exact hacc out hout
          | cons p ps ihPs =>
              intro acc out hout hacc
              rcases p with ⟨a, c⟩
              simp only [List.foldl_cons] at hout
              have hnext :
                  ∀ b ∈ acc.flatMap (fun bd => addVarEquality bd a c n),
                    AssignmentValuesNonVar b := by
                intro b hb
                rcases List.mem_flatMap.mp hb with ⟨seed, hseed, hadd⟩
                exact ihEq hadd (hacc seed hseed)
              exact ihPs hout hnext
        have hafter :
            ∀ b ∈ right.assignments.foldl
              (fun acc (v, val) =>
                acc.flatMap fun bd => addVarBinding bd v val n) [left],
              AssignmentValuesNonVar b := by
          intro b hb
          exact
            hAssignFold right.assignments hb
              (by
                intro b hb
                simp at hb
                subst b
                exact hleft)
              (by
                intro p hp
                exact hright hp)
        exact hEqFold right.equalities h hafter
      · intro b v val out h hb hval
        cases hlookup : b.lookup v with
        | none =>
            simp [addVarBinding, hlookup] at h
            subst out
            exact
              AssignmentValuesNonVar.assign_of_lookup_none
                hb hlookup hval
        | some prev =>
            by_cases hpeq : prev = val
            · simp [addVarBinding, hlookup, hpeq] at h
              subst out
              exact hb
            · simp [addVarBinding, hlookup, hpeq] at h
              rcases h with ⟨mb, hmb, hmerge⟩
              exact ihMerge hmerge hb (ihAtoms hmb)
      · intro b a c out h hb
        cases hA : b.lookup a <;> cases hC : b.lookup c <;>
          simp [addVarEquality, hA, hC] at h
        · subst out
          exact
            AssignmentValuesNonVar.addEquality
              (AssignmentValuesNonVar.removeAssignment hb c) a c
        · subst out
          exact
            AssignmentValuesNonVar.addEquality
              (AssignmentValuesNonVar.removeAssignment hb c) a c
        · subst out
          exact
            AssignmentValuesNonVar.addEquality
              (AssignmentValuesNonVar.removeAssignment hb c) a c
        · rename_i av cv
          by_cases hEq : av = cv
          · simp [hEq] at h
            subst out
            exact
              AssignmentValuesNonVar.addEquality
                (AssignmentValuesNonVar.removeAssignment hb c) a c
          · simp [hEq] at h
            rcases h with ⟨mb, hmb, hmerge⟩
            exact ihMerge hmerge hb (ihAtoms hmb)

private theorem matchAtoms_assignmentsNonVar
    {l r : Atom} {b : Bindings} {fuel : Nat}
    (h : b ∈ matchAtoms l r fuel) :
    AssignmentValuesNonVar b :=
  (matcherAssignmentsNonVar fuel).1 h

private theorem matchAtomsList_assignmentsNonVar
    {ls rs : List Atom} {acc : List Bindings} {b : Bindings} {fuel : Nat}
    (h : b ∈ matchAtomsList ls rs acc fuel)
    (hacc : ∀ seed ∈ acc, AssignmentValuesNonVar seed) :
    AssignmentValuesNonVar b :=
  (matcherAssignmentsNonVar fuel).2.1 h hacc

private theorem mergeBindings_assignmentsNonVar
    {left right out : Bindings} {fuel : Nat}
    (h : out ∈ mergeBindings left right fuel)
    (hleft : AssignmentValuesNonVar left)
    (hright : AssignmentValuesNonVar right) :
    AssignmentValuesNonVar out :=
  (matcherAssignmentsNonVar fuel).2.2.1 h hleft hright

mutual

private theorem MatchRel.assignmentsNonVar
    {l r : Atom} {b : Bindings}
    (h : MatchRel l r b) :
    AssignmentValuesNonVar b := by
  cases h with
  | symSym =>
      exact AssignmentValuesNonVar.empty
  | varVar =>
      exact AssignmentValuesNonVar.empty
  | @varNonVar v r hnv =>
      cases r with
      | symbol s =>
          exact assignmentValuesNonVar_of_singleton_assign rfl
      | grounded g =>
          exact assignmentValuesNonVar_of_singleton_assign rfl
      | expression es =>
          exact assignmentValuesNonVar_of_singleton_assign rfl
      | var w =>
          simp [Atom.isVarB] at hnv
  | @nonVarVar l v hnv =>
      cases l with
      | symbol sym =>
          exact assignmentValuesNonVar_of_singleton_assign rfl
      | grounded g =>
          exact assignmentValuesNonVar_of_singleton_assign rfl
      | expression es =>
          exact assignmentValuesNonVar_of_singleton_assign rfl
      | var w =>
          simp [Atom.isVarB] at hnv
  | grounded =>
      exact AssignmentValuesNonVar.empty
  | expr hlist =>
      exact MatchListAccRel.assignmentsNonVar hlist AssignmentValuesNonVar.empty

private theorem MatchListAccRel.assignmentsNonVar
    {ls rs : List Atom} {seed out : Bindings}
    (h : MatchListAccRel ls rs seed out)
    (hseed : AssignmentValuesNonVar seed) :
    AssignmentValuesNonVar out := by
  cases h with
  | nil =>
      exact hseed
  | @cons l r ls rs seed bH bNext bOut fuel hHead hMerge hTail =>
      have hHeadVals : AssignmentValuesNonVar bH :=
        MatchRel.assignmentsNonVar hHead
      have hNextVals : AssignmentValuesNonVar bNext :=
        mergeBindings_assignmentsNonVar hMerge hseed hHeadVals
      exact MatchListAccRel.assignmentsNonVar hTail hNextVals

end

private theorem MatchRel.noVar
    {l r : Atom} {b : Bindings}
    (h : MatchRel l r b) :
    NoVarAssignmentValues b :=
  AssignmentValuesNonVar.noVar (MatchRel.assignmentsNonVar h)

private theorem MatchListAccRel.noVar
    {ls rs : List Atom} {seed out : Bindings}
    (h : MatchListAccRel ls rs seed out)
    (hseed : AssignmentValuesNonVar seed) :
    NoVarAssignmentValues out :=
  AssignmentValuesNonVar.noVar (MatchListAccRel.assignmentsNonVar h hseed)

/-- On the no-variable-values fragment, HE bindings are loop-free: every
    successful lookup terminates immediately at a non-variable payload, so
    `hasLoopFrom` can never follow an edge. -/
private theorem NoVarAssignmentValues.hasLoop_false {b : Bindings}
    (hno : NoVarAssignmentValues b) :
    b.hasLoop = false := by
  unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop
  rw [List.any_eq_false]
  intro p hp
  rcases p with ⟨v, val⟩
  simp
  rcases lookup_some_of_mem_assignment hp with ⟨a', hlookup⟩
  cases a' with
  | var w =>
      exact False.elim (hno hlookup)
  | symbol s =>
      unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop.hasLoopFrom
      simp [Bindings.lookup, hlookup]
  | grounded g =>
      unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop.hasLoopFrom
      simp [Bindings.lookup, hlookup]
  | expression es =>
      unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop.hasLoopFrom
      simp [Bindings.lookup, hlookup]

private theorem AssignmentValuesNonVar.hasLoop_false {b : Bindings}
    (hvals : AssignmentValuesNonVar b) :
    b.hasLoop = false :=
  NoVarAssignmentValues.hasLoop_false (AssignmentValuesNonVar.noVar hvals)

private theorem matchAtomsList_length_eq_of_mem
    {ls rs : List Atom} {acc : List Bindings} {b : Bindings} {fuel : Nat}
    (h : b ∈ matchAtomsList ls rs acc fuel) :
    ls.length = rs.length := by
  induction fuel generalizing ls rs acc with
  | zero =>
      simp [matchAtomsList] at h
  | succ n ih =>
      cases ls <;> cases rs <;> simp [matchAtomsList] at h
      case nil.nil =>
        rfl
      case cons.cons l ls r rs =>
        simpa using congrArg Nat.succ
          (ih
            (ls := ls)
            (rs := rs)
            (acc := List.flatMap
              (fun a => List.flatMap (fun b => mergeBindings a b n) (matchAtoms l r n))
              acc)
            h)

mutual

private theorem matchRel_completeWitness
    {l r : Atom} {b : Bindings}
    (h : MatchRel l r b) :
    ∃ fuel, b ∈ matchAtoms l r fuel := by
  cases h with
  | symSym s =>
      have hloop : Bindings.empty.hasLoop = false :=
        AssignmentValuesNonVar.hasLoop_false AssignmentValuesNonVar.empty
      refine ⟨1, ?_⟩
      simpa [matchAtoms, getMetaType, Atom.symbolType, hloop, Bindings.empty]
  | varVar a c =>
      have hvals :
          AssignmentValuesNonVar (Bindings.empty.addEquality a c) :=
        AssignmentValuesNonVar.addEquality AssignmentValuesNonVar.empty a c
      have hloop : (Bindings.empty.addEquality a c).hasLoop = false :=
        AssignmentValuesNonVar.hasLoop_false hvals
      refine ⟨1, ?_⟩
      simpa [matchAtoms, getMetaType, Atom.variableType, hloop,
        Bindings.empty, Bindings.addEquality]
  | @varNonVar v r hnv =>
      cases r with
      | symbol s =>
          have hvals :
              AssignmentValuesNonVar (Bindings.empty.assign v (.symbol s)) :=
            assignmentValuesNonVar_of_singleton_assign rfl
          have hloop : (Bindings.empty.assign v (.symbol s)).hasLoop = false :=
            AssignmentValuesNonVar.hasLoop_false hvals
          refine ⟨1, ?_⟩
          simpa [matchAtoms, getMetaType, Atom.variableType, Atom.symbolType,
            hloop, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]
      | grounded g =>
          have hvals :
              AssignmentValuesNonVar (Bindings.empty.assign v (.grounded g)) :=
            assignmentValuesNonVar_of_singleton_assign rfl
          have hloop : (Bindings.empty.assign v (.grounded g)).hasLoop = false :=
            AssignmentValuesNonVar.hasLoop_false hvals
          refine ⟨1, ?_⟩
          simpa [matchAtoms, getMetaType, Atom.variableType, Atom.groundedType,
            hloop, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]
      | expression es =>
          have hvals :
              AssignmentValuesNonVar (Bindings.empty.assign v (.expression es)) :=
            assignmentValuesNonVar_of_singleton_assign rfl
          have hloop : (Bindings.empty.assign v (.expression es)).hasLoop = false :=
            AssignmentValuesNonVar.hasLoop_false hvals
          refine ⟨1, ?_⟩
          simpa [matchAtoms, getMetaType, Atom.variableType, Atom.expressionType,
            hloop, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]
      | var w =>
          simp [Atom.isVarB] at hnv
  | @nonVarVar l v hnv =>
      cases l with
      | symbol sym =>
          have hvals :
              AssignmentValuesNonVar (Bindings.empty.assign v (.symbol sym)) :=
            assignmentValuesNonVar_of_singleton_assign rfl
          have hloop : (Bindings.empty.assign v (.symbol sym)).hasLoop = false :=
            AssignmentValuesNonVar.hasLoop_false hvals
          refine ⟨1, ?_⟩
          simpa [matchAtoms, getMetaType, Atom.variableType, Atom.symbolType,
            hloop, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]
      | grounded g =>
          have hvals :
              AssignmentValuesNonVar (Bindings.empty.assign v (.grounded g)) :=
            assignmentValuesNonVar_of_singleton_assign rfl
          have hloop : (Bindings.empty.assign v (.grounded g)).hasLoop = false :=
            AssignmentValuesNonVar.hasLoop_false hvals
          refine ⟨1, ?_⟩
          simpa [matchAtoms, getMetaType, Atom.variableType, Atom.groundedType,
            hloop, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]
      | expression es =>
          have hvals :
              AssignmentValuesNonVar (Bindings.empty.assign v (.expression es)) :=
            assignmentValuesNonVar_of_singleton_assign rfl
          have hloop : (Bindings.empty.assign v (.expression es)).hasLoop = false :=
            AssignmentValuesNonVar.hasLoop_false hvals
          refine ⟨1, ?_⟩
          simpa [matchAtoms, getMetaType, Atom.variableType, Atom.expressionType,
            hloop, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]
      | var w =>
          simp [Atom.isVarB] at hnv
  | grounded g =>
      have hloop : Bindings.empty.hasLoop = false :=
        AssignmentValuesNonVar.hasLoop_false AssignmentValuesNonVar.empty
      refine ⟨1, ?_⟩
      simpa [matchAtoms, getMetaType, Atom.groundedType, hloop, Bindings.empty]
  | @expr ls rs b hlist =>
      obtain ⟨fuel, hmem⟩ :=
        matchListAcc_completeWitness hlist AssignmentValuesNonVar.empty
      have hlen : ls.length = rs.length :=
        matchAtomsList_length_eq_of_mem hmem
      have hloop : b.hasLoop = false :=
        MatchListAccRel.noVar hlist AssignmentValuesNonVar.empty
        |> NoVarAssignmentValues.hasLoop_false
      refine ⟨fuel + 1, ?_⟩
      have hmemFilter :
          b ∈ (matchAtomsList ls rs [Bindings.empty] fuel).filter
            (fun b => !b.hasLoop) := by
        exact List.mem_filter.mpr ⟨hmem, by simp [hloop]⟩
      simpa [matchAtoms, getMetaType, Atom.expressionType, hlen] using hmemFilter

private theorem matchListAcc_completeWitness
    {ls rs : List Atom} {seed out : Bindings}
    (h : MatchListAccRel ls rs seed out)
    (hseed : AssignmentValuesNonVar seed) :
    ∃ fuel, out ∈ matchAtomsList ls rs [seed] fuel := by
  cases h with
  | nil =>
      refine ⟨1, ?_⟩
      simp [matchAtomsList]
  | @cons l r ls rs seed bH bNext bOut fuelMerge hHead hMerge hTail =>
      obtain ⟨fuelHead, hHeadMem⟩ :=
        matchRel_completeWitness hHead
      have hHeadVals : AssignmentValuesNonVar bH :=
        MatchRel.assignmentsNonVar hHead
      have hNextVals : AssignmentValuesNonVar bNext :=
        mergeBindings_assignmentsNonVar hMerge hseed hHeadVals
      obtain ⟨fuelTail, hTailMem⟩ :=
        matchListAcc_completeWitness hTail hNextVals
      obtain ⟨fuelStep, hStepMem⟩ :=
        matchAtoms_head_step_of_match_merge hHeadMem hMerge
      obtain ⟨fuel, hFull⟩ :=
        matchAtomsList_cons_of_head_tail hStepMem hTailMem
      exact ⟨fuel, hFull⟩

end

/-- Completeness of the executable matcher against the faithful declarative
    relation. Every declaratively valid HE match is produced by `matchAtoms`
    at some finite fuel. -/
theorem matchAtoms_complete {l r : Atom} {b : Bindings}
    (h : MatchRel l r b) :
    ∃ fuel, b ∈ matchAtoms l r fuel :=
  matchRel_completeWitness h

/-- Completeness of the expression/list matcher from the public empty-seed
    surface. This is the list companion to `matchAtoms_complete`. -/
theorem matchAtomsList_complete {ls rs : List Atom} {b : Bindings}
    (h : MatchListRel ls rs b) :
    ∃ fuel, b ∈ matchAtomsList ls rs [Bindings.empty] fuel :=
  matchListAcc_completeWitness h AssignmentValuesNonVar.empty

/-- Fuel monotonicity for the executable matcher: once a binding appears at some
    fuel budget, it remains present at any larger budget obtained by adding
    extra fuel. This is the small public helper later proof layers need when
    they synchronize local matcher witnesses to a common fuel. -/
theorem matchAtoms_mono
    (l r : Atom) (fuel extra : Nat) :
    ∀ {b : Bindings}, b ∈ matchAtoms l r fuel → b ∈ matchAtoms l r (fuel + extra) :=
  fun h => matchAtoms_mono_add l r fuel extra _ h

/-- The list matcher enjoys the same additive fuel monotonicity as `matchAtoms`.
    This is exported for downstream completeness proofs that reassemble
    singleton-seeded runs into one official list run. -/
theorem matchAtomsList_mono
    (ls rs : List Atom) (acc : List Bindings) (fuel extra : Nat) :
    ∀ {b : Bindings}, b ∈ matchAtomsList ls rs acc fuel →
      b ∈ matchAtomsList ls rs acc (fuel + extra) :=
  fun h => matchAtomsList_mono_add ls rs acc fuel extra _ h

/-- Additive fuel monotonicity for the executable merge surface, exported for
    the declarative merge completeness proofs. -/
theorem mergeBindings_mono
    (left right : Bindings) (fuel extra : Nat) :
    ∀ {out : Bindings}, out ∈ mergeBindings left right fuel →
      out ∈ mergeBindings left right (fuel + extra) :=
  fun h => mergeBindings_mono_add left right fuel extra _ h

end Mettapedia.Languages.MeTTa.HE.DeclMatchSpec
