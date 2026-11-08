import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TwoWayTypedVersions

/-!
# Private type variables and space parameters

The C gives a parameter whose guarded formal is a type variable named nowhere else
in the signature (`contract_entry_facts`, `uses == 1`) the entry fact ANY, and asks
nothing of it at calls to itself; a space parameter (UNINTERPRETED_SPACE) is such
an ANY parameter that some equation reads as the space of a `match`
(`contract_reads_space`).

* **A formal with private variables is a filter** (`chainCall_private_formal`): under
  functional declarations its guard continues once when the argument is typed at
  some instance of it and not at all otherwise, and the equations it adds bind only
  its variables and its own derivation variables, which no later guard and not the
  result guard reads (`Framed`, `guards_framed`, `resultGuard_framed`).
* **A private type variable asks nothing** (`chainCall_private_var`): a bare variable is
  always met, so the protocol of a row is the protocol of the row with every private
  type variable read as `%Undefined%` (`Erases`, `chainCall_erases`), and the version
  theorems carry over (`private_ground_version_eq_protocol`,
  `private_pair_version_eq_protocol`).
* **GROUND at a private formal** (`contract_private_formal`): at an argument typed at
  the instance `F τ`, the row with `F` and the row with `F τ` have one protocol, so
  the version analysed at `τ` is the protocol of the open row
  (`private_formal_version_eq_protocol`); each call's argument fixes its instance.
* **Which parameters are spaces** (`readsSpace`, `classify`): an ANY parameter some
  equation reads by name as a `match`'s space.
* **A version reads only the spaces its entry admits**: the version theorem holds
  for a protocol and a version whose views of the spaces differ everywhere but on
  the rows of the admitted spaces, since a `match` reads a space variable, which
  holds an admitted space at every call, or a space the version names, which the
  entry tests (`TwoWayTypedVersions.TAgree.rows`).
* **Controls**: `reach`, whose space parameter sits at the guarded formal `$s` of
  `(-> $s Number Number)`, is accepted, classified as the C classifies it, and its
  version, over a view of the spaces that adds a row to a space it never reads, is
  the protocol at every fuel; `(reach kb 1)` answers `0` once per row of `kb`; a
  `match` over a space the entry does not admit is declined, and the two views
  give it different rows; `len` at `(-> (List $a) Number)` is accepted at every
  instance, and through the open row's protocol `(len (Cons "s" Nil))` answers `1`
  at `$a := String` while the same version answers `2` on a list of numbers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PrivateSpaceVersions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions UnifyingFrames OpenFrameEffects CapturedUninterpretedRegions
open GroundUninterpretedVersions TwoWayTypedVersions

/-! ## A block of equations no later guard reads -/

/-- A store clear of the private variables and of the derivation variables of
position `k`. -/
def FrameClear (priv : String → Prop) (k : ℕ) (X : List (Eqn CallVar)) : Prop :=
  ∀ w ∈ eqnVars X, (∀ x, priv x → w ≠ .inl x) ∧ ∀ d, w ≠ atGuard k d

theorem FrameClear.nil (priv : String → Prop) (k : ℕ) : FrameClear priv k [] := fun w member => by
  simp [eqnVars] at member

theorem FrameClear.append {priv : String → Prop} {k : ℕ} {X Y : List (Eqn CallVar)}
    (hX : FrameClear priv k X) (hY : FrameClear priv k Y) : FrameClear priv k (X ++ Y) := fun w hw => by
  rw [eqnVars_append, List.mem_append] at hw
  exact hw.elim (hX w) (hY w)

/-- A variable of the private position's block. -/
def InBlock (priv : String → Prop) (k : ℕ) (w : CallVar) : Prop :=
  (∃ x, priv x ∧ w = .inl x) ∨ ∃ d, w = atGuard k d

/-- Stores with and without the block `B`, between parts clear of it. -/
def Framed (priv : String → Prop) (k : ℕ) (B : List (Eqn CallVar)) (So Sc : List (Eqn CallVar)) : Prop :=
  ∃ S X, So = S ++ B ++ X ∧ Sc = S ++ X ∧ FrameClear priv k S ∧ FrameClear priv k X

theorem Framed.append {priv : String → Prop} {k : ℕ} {B So Sc : List (Eqn CallVar)}
    (h : Framed priv k B So Sc) (Y : List (Eqn CallVar)) (hY : FrameClear priv k Y) :
    Framed priv k B (So ++ Y) (Sc ++ Y) := by
  obtain ⟨S, X, rfl, rfl, hS, hX⟩ := h
  exact ⟨S, X ++ Y, by simp, by simp, hS, hX.append hY⟩

theorem not_inBlock {priv : String → Prop} {k : ℕ} {X : List (Eqn CallVar)}
    (clear : FrameClear priv k X) : ∀ w ∈ eqnVars X, ¬ InBlock priv k w := by
  intro w member block
  obtain ⟨notPriv, notK⟩ := clear w member
  rcases block with ⟨x, px, same⟩ | ⟨d, same⟩
  · exact notPriv x px same
  · exact notK d same

open Classical in
/-- **A satisfiable block over its own variables changes no satisfiability.** -/
theorem Framed.sat_iff {priv : String → Prop} {k : ℕ} {B So Sc : List (Eqn CallVar)}
    (blockVars : ∀ w ∈ eqnVars B, InBlock priv k w) (satB : Sat B) (h : Framed priv k B So Sc) :
    Sat So ↔ Sat Sc := by
  obtain ⟨S, X, rfl, rfl, hS, hX⟩ := h
  constructor
  · rintro ⟨ρ, hρ⟩
    simp only [solves_append] at hρ
    exact ⟨ρ, (solves_append _ _ _).mpr ⟨hρ.1.1, hρ.2⟩⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨ρB, hρB⟩ := satB
    rw [solves_append] at hρ
    let ρ' : CallVar → Ty Empty := fun w => if InBlock priv k w then ρB w else ρ w
    refine ⟨ρ', (solves_append _ _ _).mpr ⟨(solves_append _ _ _).mpr ⟨?_, ?_⟩, ?_⟩⟩
    · exact (solves_congr fun w hw => if_neg (not_inBlock hS w hw)).mpr hρ.1
    · exact (solves_congr fun w hw => if_pos (blockVars w hw)).mpr hρB
    · exact (solves_congr fun w hw => if_neg (not_inBlock hX w hw)).mpr hρ.2

variable {Γ : Decls}

theorem frameClear_guard_ext {priv : String → Prop} {k j : ℕ} (hjk : j ≠ k) (G : Ty String)
    (hG : ∀ x ∈ G.vars, ¬ priv x) (d : Deriv) :
    FrameClear priv k (d.eqs.map (Eqn.map (atGuard j)) ++ [(d.ty.map (atGuard j), G.map Sum.inl)]) := by
  intro w hw
  rw [eqnVars_append, List.mem_append, eqnVars_map] at hw
  rcases hw with hw | hw
  · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hw
    refine ⟨fun _ _ same => (by cases same), fun d' same => ?_⟩
    simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at same
    exact hjk same.1
  · simp only [eqnVars, Eqn.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, Ty.vars_map, List.mem_map] at hw
    rcases hw with ⟨e, -, rfl⟩ | ⟨x, occurs, rfl⟩
    · refine ⟨fun _ _ same => (by cases same), fun d' same => ?_⟩
      simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at same
      exact hjk same.1
    · refine ⟨fun y py same => hG x occurs ?_, fun d' same => by cases same⟩
      simp only [Sum.inl.injEq] at same
      rw [same]
      exact py

theorem frameClear_meta {priv : String → Prop} {k : ℕ} (G : Ty String) (hG : ∀ x ∈ G.vars, ¬ priv x)
    (kn : String) : FrameClear priv k [((Ty.sym kn : Ty CallVar), G.map Sum.inl)] := by
  intro w hw
  simp only [eqnVars, Eqn.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, Ty.vars_map, List.mem_map] at hw
  rcases hw with hw | ⟨x, occurs, rfl⟩
  · simp [Ty.vars] at hw
  · refine ⟨fun y py same => hG x occurs ?_, fun d same => by cases same⟩
    simp only [Sum.inl.injEq] at same
    rw [same]
    exact py

open Classical in
/-- **A guard at another position, at a formal naming no private variable, answers
framed stores for framed stores, one for one.** -/
theorem guard_framed {priv : String → Prop} {k j : ℕ} {B So Sc : List (Eqn CallVar)}
    (blockVars : ∀ w ∈ eqnVars B, InBlock priv k w) (satB : Sat B) (hjk : j ≠ k)
    (h : Framed priv k B So Sc) (G : Ty String) (hG : ∀ x ∈ G.vars, ¬ priv x) (inf : Info)
    (kn : String) :
    Multiset.Rel (Framed priv k B) (guard (atGuard j) So (G.map Sum.inl) inf kn)
      (guard (atGuard j) Sc (G.map Sum.inl) inf kn) := by
  have rel : Multiset.Rel (Framed priv k B) (getType (atGuard j) So (G.map Sum.inl) inf)
      (getType (atGuard j) Sc (G.map Sum.inl) inf) := by
    unfold getType
    rw [Multiset.filter_map, Multiset.filter_map]
    have same : (eff inf).filter (Sat ∘ fun d => So ++ d.eqs.map (Eqn.map (atGuard j)) ++
        [(d.ty.map (atGuard j), G.map Sum.inl)]) =
        (eff inf).filter (Sat ∘ fun d => Sc ++ d.eqs.map (Eqn.map (atGuard j)) ++
          [(d.ty.map (atGuard j), G.map Sum.inl)]) :=
      Multiset.filter_congr fun d _ => by
        simp only [Function.comp, List.append_assoc]
        exact (h.append _ (frameClear_guard_ext hjk G hG d)).sat_iff blockVars satB
    rw [same, Multiset.rel_map]
    refine Multiset.rel_refl_of_refl_on fun d _ => ?_
    simp only [List.append_assoc]
    exact h.append _ (frameClear_guard_ext hjk G hG d)
  unfold guard
  rw [Multiset.card_eq_card_of_rel rel]
  split_ifs
  · rw [Multiset.filter_singleton, Multiset.filter_singleton]
    have hY := frameClear_meta (k := k) G hG kn
    by_cases hs : Sat (So ++ [((Ty.sym kn : Ty CallVar), G.map Sum.inl)])
    · rw [if_pos hs, if_pos (((h.append _ hY).sat_iff blockVars satB).mp hs)]
      exact .cons (h.append _ hY) .zero
    · rw [if_neg hs, if_neg fun hs' => hs (((h.append _ hY).sat_iff blockVars satB).mpr hs')]
      exact .zero
  · exact rel

/-- So do the guards of the positions after it. -/
theorem guards_framed {priv : String → Prop} {k : ℕ} {B : List (Eqn CallVar)}
    (blockVars : ∀ w ∈ eqnVars B, InBlock priv k w) (satB : Sat B) (kind : Atom → String) :
    ∀ (j : ℕ) (As : List (Ty String)) (vs : List Atom), k < j →
      (∀ G ∈ As, ∀ x ∈ G.vars, ¬ priv x) →
      ∀ {So Sc : List (Eqn CallVar)}, Framed priv k B So Sc →
        Multiset.Rel (Framed priv k B) (guards Γ kind j As vs So) (guards Γ kind j As vs Sc)
  | _, [], [], _, _, _, _, h => .cons h .zero
  | j, A :: As, v :: vs, hk, apart, So, Sc, h => by
      simp only [guards]
      split_ifs
      · exact Multiset.rel_bind (fun _ _ hab => guards_framed blockVars satB kind (j + 1) As vs
            (by omega) (fun G member => apart G (by simp [member])) hab)
          (guard_framed blockVars satB (by omega) h A (apart A (by simp)) _ _)
      · exact guards_framed blockVars satB kind (j + 1) As vs (by omega)
          (fun G member => apart G (by simp [member])) h
  | _, [], _ :: _, _, _, _, _, _ => by simp only [guards]; exact .zero
  | _, _ :: _, [], _, _, _, _, _ => by simp only [guards]; exact .zero

/-- **The result guard, after the position, reads framed stores alike.** -/
theorem resultGuard_framed {priv : String → Prop} {k m : ℕ} {B So Sc : List (Eqn CallVar)}
    (blockVars : ∀ w ∈ eqnVars B, InBlock priv k w) (satB : Sat B) (kind : Atom → String)
    (hmk : m ≠ k) (R : Ty String) (hR : ∀ x ∈ R.vars, ¬ priv x) (h : Framed priv k B So Sc)
    (r : Atom) : resultGuard Γ kind m R So r = resultGuard Γ kind m R Sc r := by
  unfold resultGuard
  split_ifs
  · rw [Multiset.map_const', Multiset.map_const',
      Multiset.card_eq_card_of_rel (guard_framed blockVars satB hmk h R hR (info Γ r) (kind r))]
  · rfl

theorem mem_guard {U : Type} {e : DVar → U} {S S' : List (Eqn U)} {T : Ty U} {j : Info} {kn : String}
    (member : S' ∈ guard e S T j kn) :
    (∃ d ∈ eff j, S' = S ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T)]) ∨ S' = S ++ [(.sym kn, T)] := by
  classical
  unfold guard at member
  split_ifs at member
  · right
    exact Multiset.mem_singleton.mp (Multiset.mem_of_mem_filter member)
  · left
    unfold getType at member
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_mem_filter member)
    exact ⟨d, hd, rfl⟩

theorem sat_of_mem_guard {U : Type} {e : DVar → U} {S S' : List (Eqn U)} {T : Ty U} {j : Info}
    {kn : String} (member : S' ∈ guard e S T j kn) : Sat S' := by
  classical
  unfold guard at member
  split_ifs at member
  · exact (Multiset.mem_filter.mp member).2
  · unfold getType at member
    exact (Multiset.mem_filter.mp member).2

theorem guards_sat (kind : Atom → String) :
    ∀ (j : ℕ) (As : List (Ty String)) (vs : List Atom) (S : List (Eqn CallVar)), Sat S →
      ∀ S' ∈ guards Γ kind j As vs S, Sat S'
  | _, [], [], S, sat, S', member => by
      simp only [guards, Multiset.mem_singleton] at member
      rw [member]
      exact sat
  | j, A :: As, v :: vs, S, sat, S', member => by
      simp only [guards] at member
      split_ifs at member
      · obtain ⟨S₁, present, member⟩ := Multiset.mem_bind.mp member
        exact guards_sat kind (j + 1) As vs S₁ (sat_of_mem_guard present) S' member
      · exact guards_sat kind (j + 1) As vs S sat S' member
  | _, [], _ :: _, _, _, S', member => by simp [guards] at member
  | _, _ :: _, [], _, _, S', member => by simp [guards] at member

/-- The guards before the private position leave the store clear of its block. -/
theorem guards_clear {priv : String → Prop} {k : ℕ} (kind : Atom → String) :
    ∀ (j : ℕ) (As : List (Ty String)) (vs : List Atom) (S : List (Eqn CallVar)),
      j + As.length ≤ k → (∀ G ∈ As, ∀ x ∈ G.vars, ¬ priv x) → FrameClear priv k S →
        ∀ S' ∈ guards Γ kind j As vs S, FrameClear priv k S'
  | _, [], [], S, _, _, clear, S', member => by
      simp only [guards, Multiset.mem_singleton] at member
      rw [member]
      exact clear
  | j, A :: As, v :: vs, S, le, apart, clear, S', member => by
      simp only [List.length_cons] at le
      simp only [guards] at member
      split_ifs at member
      · obtain ⟨S₁, present, member⟩ := Multiset.mem_bind.mp member
        refine guards_clear kind (j + 1) As vs S₁ (by omega)
          (fun G member => apart G (by simp [member])) ?_ S' member
        rcases mem_guard present with ⟨d, _, rfl⟩ | rfl
        · rw [List.append_assoc]
          exact clear.append (frameClear_guard_ext (by omega) A (apart A (by simp)) d)
        · exact clear.append (frameClear_meta A (apart A (by simp)) _)
      · exact guards_clear kind (j + 1) As vs S (by omega)
          (fun G member => apart G (by simp [member])) clear S' member
  | _, [], _ :: _, _, _, _, _, S', member => by simp [guards] at member
  | _, _ :: _, [], _, _, _, _, S', member => by simp [guards] at member

/-! ## A guard at a formal whose variables are private -/

/-- The equations the guard at position `k` adds for the formal `F` on a value whose
one derivation is `d`. -/
def block (k : ℕ) (d : Deriv) (F : Ty String) : List (Eqn CallVar) :=
  d.eqs.map (Eqn.map (atGuard k)) ++ [(d.ty.map (atGuard k), F.map Sum.inl)]

theorem block_vars (k : ℕ) (d : Deriv) (F : Ty String) :
    ∀ w ∈ eqnVars (block k d F), InBlock (· ∈ F.vars) k w := by
  intro w hw
  rw [block, eqnVars_append, List.mem_append, eqnVars_map] at hw
  rcases hw with hw | hw
  · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hw
    exact .inr ⟨e, rfl⟩
  · simp only [eqnVars, Eqn.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, Ty.vars_map, List.mem_map] at hw
    rcases hw with ⟨e, -, rfl⟩ | ⟨x, occurs, rfl⟩
    · exact .inr ⟨e, rfl⟩
    · exact .inl ⟨x, occurs, rfl⟩

open Classical in
/-- **The block is satisfiable exactly when the value is typed at some instance of the
formal**, under functional declarations. -/
theorem sat_block_iff (hΓ : Functional Γ) (k : ℕ) (v : Atom) (F : Ty String) :
    Sat (block k (theDeriv hΓ v) F) ↔ ∃ τ : String → Ty Empty, count (info Γ v) (F.bind τ) = 1 := by
  set d := theDeriv hΓ v with hd
  constructor
  · rintro ⟨ρ, solved⟩
    rw [block, solves_append, solves_map, solves_singleton, Ty.bind_map, Ty.bind_map] at solved
    refine ⟨ρ ∘ Sum.inl, ?_⟩
    rw [count_eq_ite hΓ, ← hd, if_pos]
    refine ⟨ρ ∘ atGuard k, (solves_append _ _ _).mpr ⟨solved.1, (solves_singleton _ _).mpr ?_⟩⟩
    rw [Ty.lift_bind_ground]
    exact solved.2
  · rintro ⟨τ, typed⟩
    rw [count_eq_ite hΓ, ← hd] at typed
    split_ifs at typed with h
    obtain ⟨ρ, solved⟩ := h
    rw [solves_append, solves_singleton, Ty.lift_bind_ground] at solved
    refine ⟨fun w => match w with
      | .inl x => τ x
      | .inr (_, e) => ρ e, ?_⟩
    rw [block, solves_append, solves_map, solves_singleton, Ty.bind_map, Ty.bind_map]
    exact ⟨solved.1, solved.2⟩

theorem guards_cons (kind : Atom → String) (k : ℕ) (A : Ty String) (As : List (Ty String)) (v : Atom)
    (vs : List Atom) (S : List (Eqn CallVar)) :
    guards Γ kind k (A :: As) (v :: vs) S =
      if demand A = .guarded then
        (guard (atGuard k) S (A.map Sum.inl) (info Γ v) (kind v)).bind (guards Γ kind (k + 1) As vs)
      else guards Γ kind (k + 1) As vs S := rfl

/-- A bare type variable's block is always satisfiable. -/
theorem sat_block_var (hΓ : Functional Γ) (k : ℕ) (v : Atom) (s : String) :
    Sat (block k (theDeriv hΓ v) (.var s)) := by
  obtain ⟨ρd, hρd⟩ := theDeriv_sat hΓ v
  refine ⟨fun w => match w with
    | .inl _ => (theDeriv hΓ v).ty.bind ρd
    | .inr (_, e) => ρd e, (solves_append _ _ _).mpr ⟨(solves_map _ _ _).mpr ?_, ?_⟩⟩
  · exact hρd
  · rw [solves_singleton]
    simp only [Ty.bind_map, Ty.bind_var', Ty.map_var]
    rfl

open Classical in
/-- **The guard at a formal whose variables are private**, on a store clear of them:
once, with the block, when the value is typed at some instance of the formal; not at
all otherwise. -/
theorem guard_private (hΓ : Functional Γ) (grounded : String → Bool) (k : ℕ)
    (S : List (Eqn CallVar)) (v : Atom) (F : Ty String) (fallback : NoMeta F ∨ ∃ s, F = .var s)
    (satS : Sat S) (clearS : FrameClear (· ∈ F.vars) k S) :
    guard (atGuard k) S (F.map Sum.inl) (info Γ v) (metatype grounded v) =
      if ∃ τ : String → Ty Empty, count (info Γ v) (F.bind τ) = 1 then
        {S ++ block k (theDeriv hΓ v) F} else 0 := by
  have gt := getType_of_eff (atGuard k) S (F.map Sum.inl) (eff_theDeriv hΓ v)
  rw [show S ++ (theDeriv hΓ v).eqs.map (Eqn.map (atGuard k)) ++
      [((theDeriv hΓ v).ty.map (atGuard k), F.map Sum.inl)] = S ++ block k (theDeriv hΓ v) F by
    rw [block, List.append_assoc]] at gt
  have satIff : Sat (S ++ block k (theDeriv hΓ v) F) ↔
      ∃ τ : String → Ty Empty, count (info Γ v) (F.bind τ) = 1 := by
    rw [← sat_block_iff hΓ k v F]
    constructor
    · exact Sat.right
    · intro satB
      have framed : Framed (· ∈ F.vars) k (block k (theDeriv hΓ v) F)
          (S ++ block k (theDeriv hΓ v) F ++ []) (S ++ []) :=
        ⟨S, [], rfl, rfl, clearS, FrameClear.nil _ _⟩
      simpa using (framed.sat_iff (block_vars k _ F) satB).mpr (by simpa using satS)
  by_cases typed : ∃ τ : String → Ty Empty, count (info Γ v) (F.bind τ) = 1
  · rw [if_pos (satIff.mpr typed)] at gt
    rw [if_pos typed, guard_of_getType _ _ _ _ _ (by rw [gt]; exact Multiset.singleton_ne_zero _), gt]
  · rw [if_neg (fun sat => typed (satIff.mp sat))] at gt
    rw [if_neg typed]
    rcases fallback with noMeta | ⟨s, rfl⟩
    · unfold guard
      rw [gt, Multiset.card_zero, if_pos rfl, Multiset.filter_singleton,
        if_neg (not_sat_meta noMeta grounded _)]
      rfl
    · exact absurd ((sat_block_iff hΓ k v _).mp (sat_block_var hΓ k v s)) typed

open Classical in
/-- **A formal whose variables no other formal and not the range names is a filter,
not a check that couples**: under functional declarations its guard continues once
when the argument is typed at some instance of it, and not at all otherwise, and
what it binds no other guard reads. A bare variable is always met
(`chainCall_private_var`); a named formal such as `(List $a)` is the C's private
formal (`contract_private_formal`). -/
theorem chainCall_private_formal (hΓ : Functional Γ) (grounded : String → Bool)
    (body : List Atom → Multiset Atom) (pre post : List (Ty String)) (R : Ty String) (F : Ty String)
    (guarded : demand F = .guarded) (fallback : NoMeta F ∨ ∃ s, F = .var s) (us ws : List Atom)
    (v : Atom) (len : pre.length = us.length) (preApart : ∀ G ∈ pre, ∀ x ∈ G.vars, x ∉ F.vars)
    (postApart : ∀ G ∈ post, ∀ x ∈ G.vars, x ∉ F.vars) (rangeApart : ∀ x ∈ R.vars, x ∉ F.vars) :
    chainCall Γ (metatype grounded) body (arrow (pre ++ F :: post) R) (us ++ v :: ws) =
      (if ∃ τ : String → Ty Empty, count (info Γ v) (F.bind τ) = 1 then 1 else 0) •
        chainCall Γ (metatype grounded) body (arrow (pre ++ .sym "%Undefined%" :: post) R)
          (us ++ v :: ws) := by
  unfold chainCall
  rw [arrowSplit_arrow, arrowSplit_arrow]
  dsimp only
  have lenEq : (pre ++ F :: post).length = (pre ++ (Ty.sym "%Undefined%" : Ty String) :: post).length := by
    simp
  rw [lenEq, guards_append (metatype grounded) 0 pre _ us _ [] len,
    guards_append (metatype grounded) 0 pre _ us _ [] len, Multiset.bind_assoc, Multiset.bind_assoc]
  simp only [zero_add]
  have unguarded : demand (Ty.sym "%Undefined%" : Ty String) ≠ .guarded := by decide
  split_ifs with typed
  · rw [one_nsmul]
    refine Multiset.bind_congr fun S member => ?_
    have satS : Sat S := guards_sat (metatype grounded) 0 pre us [] sat_nil S member
    have clearS : FrameClear (· ∈ F.vars) pre.length S :=
      guards_clear (metatype grounded) 0 pre us [] (by simp) preApart (FrameClear.nil _ _) S member
    have satB : Sat (block pre.length (theDeriv hΓ v) F) := (sat_block_iff hΓ _ v F).mpr typed
    rw [guards_cons, if_pos guarded, guard_private hΓ grounded _ S v F fallback satS clearS,
      if_pos typed, Multiset.singleton_bind, guards_cons, if_neg unguarded]
    have related := guards_framed (Γ := Γ) (block_vars pre.length (theDeriv hΓ v) F) satB
      (metatype grounded) (pre.length + 1) post ws (by omega) postApart
      (⟨S, [], rfl, rfl, clearS, FrameClear.nil _ _⟩ :
        Framed (· ∈ F.vars) pre.length (block pre.length (theDeriv hΓ v) F)
          (S ++ block pre.length (theDeriv hΓ v) F ++ []) (S ++ []))
    simp only [List.append_nil] at related
    rw [← Multiset.rel_eq]
    refine Multiset.rel_bind (fun So Sc framed => ?_) related
    rw [Multiset.rel_eq]
    refine Multiset.bind_congr fun r _ => ?_
    exact resultGuard_framed (block_vars pre.length (theDeriv hΓ v) F) satB (metatype grounded)
      (by simp) R rangeApart framed r
  · rw [zero_nsmul]
    refine (Multiset.bind_congr (g := fun _ => 0) fun S member => ?_).trans (Multiset.bind_zero _)
    have satS : Sat S := guards_sat (metatype grounded) 0 pre us [] sat_nil S member
    have clearS : FrameClear (· ∈ F.vars) pre.length S :=
      guards_clear (metatype grounded) 0 pre us [] (by simp) preApart (FrameClear.nil _ _) S member
    rw [guards_cons, if_pos guarded, guard_private hΓ grounded _ S v F fallback satS clearS,
      if_neg typed, Multiset.zero_bind, Multiset.zero_bind]

/-! ## A guard at a private type variable is no check -/

theorem var_typed (hΓ : Functional Γ) (v : Atom) (s : String) :
    ∃ τ : String → Ty Empty, count (info Γ v) ((Ty.var s : Ty String).bind τ) = 1 :=
  (sat_block_iff hΓ 0 v _).mp (sat_block_var hΓ 0 v s)

/-- **Under functional declarations, a parameter at a type variable no other formal
and not the range names asks nothing**: its guard continues once whatever the
argument, binding only the variable, which no other guard reads. This is the C's
ANY entry fact at a guarded formal (`contract_entry_facts`, `uses == 1`). -/
theorem chainCall_private_var (hΓ : Functional Γ) (grounded : String → Bool)
    (body : List Atom → Multiset Atom) (pre post : List (Ty String)) (R : Ty String) (s : String)
    (us ws : List Atom) (v : Atom) (len : pre.length = us.length) (preApart : ∀ F ∈ pre, s ∉ F.vars)
    (postApart : ∀ F ∈ post, s ∉ F.vars) (rangeApart : s ∉ R.vars) :
    chainCall Γ (metatype grounded) body (arrow (pre ++ .var s :: post) R) (us ++ v :: ws) =
      chainCall Γ (metatype grounded) body (arrow (pre ++ .sym "%Undefined%" :: post) R)
        (us ++ v :: ws) := by
  have guardedVar : demand (Ty.var s : Ty String) = .guarded := by
    unfold demand
    rw [if_neg (fun h => by cases h), if_neg (show ¬ Unchecked (Ty.var s : Ty String) from fun h => h)]
  have apart : ∀ (G : Ty String), s ∉ G.vars → ∀ x ∈ G.vars, x ∉ (Ty.var s : Ty String).vars :=
    fun G notIn x occurs same => notIn (by simp only [Ty.vars_var, List.mem_singleton] at same; exact same ▸ occurs)
  rw [chainCall_private_formal hΓ grounded body pre post R (.var s) guardedVar (.inr ⟨s, rfl⟩) us ws v len
    (fun G member => apart G (preApart G member)) (fun G member => apart G (postApart G member))
    (apart R rangeApart), if_pos (var_typed hΓ v s), one_nsmul]

/-- **The formals a version reads alike**: each type variable no other formal and
not the range names replaced by `%Undefined%`, one at a time. -/
inductive Erases (R : Ty String) : List (Ty String) → List (Ty String) → Prop
  | refl (Fs : List (Ty String)) : Erases R Fs Fs
  | step {pre post Gs : List (Ty String)} {s : String} :
      (∀ F ∈ pre, s ∉ F.vars) → (∀ F ∈ post, s ∉ F.vars) → s ∉ R.vars →
      Erases R (pre ++ .sym "%Undefined%" :: post) Gs → Erases R (pre ++ .var s :: post) Gs

theorem Erases.length {R : Ty String} {Fs Gs : List (Ty String)} (h : Erases R Fs Gs) :
    Fs.length = Gs.length := by
  induction h with
  | refl => rfl
  | step _ _ _ _ ih => simpa using ih

theorem split_at_length {α : Type} (vs : List α) (k m : ℕ) (len : vs.length = k + (m + 1)) :
    ∃ us v ws, vs = us ++ v :: ws ∧ us.length = k := by
  refine ⟨vs.take k, (vs.drop k).head (by simp [List.drop_eq_nil_iff]; omega),
    (vs.drop k).tail, ?_, by simp; omega⟩
  rw [List.cons_head_tail, List.take_append_drop]

/-- **Private type variables ask nothing, at every position**: a row and its erased
formals have one protocol. -/
theorem chainCall_erases (hΓ : Functional Γ) (grounded : String → Bool) (body : List Atom → Multiset Atom)
    {R : Ty String} {Fs Gs : List (Ty String)} (h : Erases R Fs Gs) :
    ∀ vs : List Atom, Fs.length = vs.length →
      chainCall Γ (metatype grounded) body (arrow Fs R) vs =
        chainCall Γ (metatype grounded) body (arrow Gs R) vs := by
  induction h with
  | refl => intro _ _; rfl
  | @step pre post Gs s preApart postApart rangeApart rest ih =>
      intro vs len
      obtain ⟨us, v, ws, rfl, ulen⟩ := split_at_length vs pre.length post.length (by simpa using len.symm)
      rw [chainCall_private_var hΓ grounded body pre post R s us ws v ulen.symm preApart postApart rangeApart]
      exact ih _ (by simpa using len)

/-! ## Versions whose ANY and space parameters sit at private type variables -/

section Versions

variable {grounded : String → Bool} {Ok : Atom → Prop} {P : TProgram} {E E' : Env}
  {eqs : List Equation} {enP enV : String → List Atom → Multiset Atom}

theorem rowReduces_of_erases (hΓ : Functional Γ) {R : Ty String} {Fs Gs : List (Ty String)}
    (h : Erases R Fs Gs) (len : Fs.length = P.positions.length)
    (reduces : RowReduces Γ grounded Ok P (arrow Gs R)) : RowReduces Γ grounded Ok P (arrow Fs R) := by
  intro b ws admitted answers
  rw [chainCall_erases hΓ _ b h ws (len.trans admitted.length_eq)]
  exact reduces b ws admitted answers

/-- **GROUND, ANY and space parameters, the latter at private type variables**: the
protocol of `(-> F₁ … Fₖ R)`, where each ANY or space parameter's formal is
`%Undefined%`, `_` or a type variable no other formal and not the range names, is the
version at every fuel, multiplicity included. -/
theorem private_ground_version_eq_protocol (h : TVersionHyps Γ grounded Ok P E E' eqs enP enV)
    {As : List (Ty Empty)} {R : Ty Empty} {Fs : List (Ty String)}
    (formals : List.Forall₂ ClosedFormal P.positions As) (range : RangeFormal P.result R)
    (erases : Erases R.lift Fs (As.map Ty.lift)) (n : ℕ) (ws : List Atom)
    (admitted : TAdmitted Γ grounded Ok P.positions ws) :
    protocolRun Γ grounded (relBody E enP eqs) (arrow Fs R.lift) n ws =
      versionRun (relBody E' enV eqs) n ws :=
  typed_version_eq_protocol h (rowReduces_of_erases h.functional erases
    (by rw [erases.length, List.length_map, formals.length_eq])
    (rowReduces_closed formals range)) n ws admitted

/-- **The pair beside them**: the same for `(-> F₁ … $t … Fₖ $t)`. -/
theorem private_pair_version_eq_protocol (h : TVersionHyps Γ grounded Ok P E E' eqs enP enV)
    {pre post : List Pos} {Apre Apost : List (Ty Empty)} {Fs : List (Ty String)} (t : String)
    (shape : P.positions = pre ++ .pair :: post) (result : P.result = .pair)
    (preFormals : List.Forall₂ ClosedFormal pre Apre) (postFormals : List.Forall₂ ClosedFormal post Apost)
    (erases : Erases (.var t) Fs (Apre.map Ty.lift ++ .var t :: Apost.map Ty.lift)) (n : ℕ)
    (ws : List Atom) (admitted : TAdmitted Γ grounded Ok P.positions ws) :
    protocolRun Γ grounded (relBody E enP eqs) (arrow Fs (.var t)) n ws =
      versionRun (relBody E' enV eqs) n ws :=
  typed_version_eq_protocol h (rowReduces_of_erases h.functional erases
    (by rw [erases.length, shape]; simp [preFormals.length_eq, postFormals.length_eq])
    (rowReduces_pair t shape result preFormals postFormals)) n ws admitted

theorem split_forall₂ {α β : Type} {Rel : α → β → Prop} :
    ∀ {Pre : List α} {q : α} {Post : List α} {ws : List β}, List.Forall₂ Rel (Pre ++ q :: Post) ws →
      ∃ us v rest, ws = us ++ v :: rest ∧ us.length = Pre.length ∧ Rel q v
  | [], _, _, _ :: _, .cons here _ => ⟨[], _, _, rfl, rfl, here⟩
  | _ :: _, _, _, _ :: _, .cons _ rest => by
      obtain ⟨us, v, more, rfl, len, here⟩ := split_forall₂ rest
      exact ⟨_ :: us, v, more, rfl, by simp [len], here⟩

/-- **A private formal reduces like its instance**: at arguments typed at the instance
`F τ`, the row with the private formal `F` and the row with the closed formal `F τ`
have one protocol, so the closed row's reduction gives the open row's. -/
theorem rowReduces_private_formal (hΓ : Functional Γ) {Pre Post : List Pos}
    {pre post : List (Ty String)} {R : Ty String} {F : Ty String} (τ : String → Ty Empty)
    (shape : P.positions = Pre ++ .ground (F.bind τ) :: Post) (lenPre : pre.length = Pre.length)
    (guarded : demand F = .guarded) (noMeta : NoMeta F)
    (preApart : ∀ G ∈ pre, ∀ x ∈ G.vars, x ∉ F.vars) (postApart : ∀ G ∈ post, ∀ x ∈ G.vars, x ∉ F.vars)
    (rangeApart : ∀ x ∈ R.vars, x ∉ F.vars)
    (reduces : RowReduces Γ grounded Ok P (arrow (pre ++ (F.bind τ).lift :: post) R)) :
    RowReduces Γ grounded Ok P (arrow (pre ++ F :: post) R) := by
  intro b ws admitted answers
  have split := admitted
  rw [shape] at split
  obtain ⟨us, v, rest, rfl, ulen, here⟩ := split_forall₂ split
  have typed : count (info Γ v) (F.bind τ) = 1 := here.2.count (noMeta τ)
  have closedGuarded : demand ((F.bind τ).lift : Ty String) = .guarded := by
    rw [demand_bind_lift noMeta.not_var τ]
    exact guarded
  have closedNoMeta : NoMeta ((F.bind τ).lift : Ty String) := fun σ => by
    rw [Ty.lift_bind_ground]
    exact noMeta τ
  have noVars : ∀ (G : Ty String), ∀ x ∈ G.vars, x ∉ ((F.bind τ).lift : Ty String).vars :=
    fun G x _ => by simp
  rw [chainCall_private_formal hΓ grounded b pre post R F guarded (.inl noMeta) us rest v
      (lenPre.trans ulen.symm) preApart postApart rangeApart, if_pos ⟨τ, typed⟩, one_nsmul,
    ← reduces b (us ++ v :: rest) admitted answers,
    chainCall_private_formal hΓ grounded b pre post R ((F.bind τ).lift) closedGuarded
      (.inl closedNoMeta) us rest v (lenPre.trans ulen.symm) (fun G _ => noVars G) (fun G _ => noVars G)
      (noVars R),
    if_pos ⟨τ, by rw [Ty.lift_bind_ground]; exact typed⟩, one_nsmul]

/-- **GROUND at a private formal under logic variables** (`contract_private_formal`): the
version analysed at an instance `τ` of the private formal `F`, its other formals
closed, is the protocol of the row with `F` itself at every fuel, multiplicity
included, at arguments ground and typed at `F τ`. Each call is at some instance, which
its argument fixes, so the theorem at every `τ` covers every call the C admits. -/
theorem private_formal_version_eq_protocol (h : TVersionHyps Γ grounded Ok P E E' eqs enP enV)
    {Pre Post : List Pos} {pre post : List (Ty String)} {R : Ty String} {F : Ty String}
    (τ : String → Ty Empty) (shape : P.positions = Pre ++ .ground (F.bind τ) :: Post)
    (lenPre : pre.length = Pre.length) (guarded : demand F = .guarded) (noMeta : NoMeta F)
    (preApart : ∀ G ∈ pre, ∀ x ∈ G.vars, x ∉ F.vars) (postApart : ∀ G ∈ post, ∀ x ∈ G.vars, x ∉ F.vars)
    (rangeApart : ∀ x ∈ R.vars, x ∉ F.vars)
    (reduces : RowReduces Γ grounded Ok P (arrow (pre ++ (F.bind τ).lift :: post) R)) (n : ℕ)
    (ws : List Atom) (admitted : TAdmitted Γ grounded Ok P.positions ws) :
    protocolRun Γ grounded (relBody E enP eqs) (arrow (pre ++ F :: post) R) n ws =
      versionRun (relBody E' enV eqs) n ws :=
  typed_version_eq_protocol h (rowReduces_private_formal h.functional τ shape lenPre guarded noMeta
    preApart postApart rangeApart reduces) n ws admitted

end Versions

/-! ## Which parameters are spaces (`contract_reads_space`) -/

mutual
/-- Whether a `match` in the expression reads the variable as its space. -/
def readsSpace (x : String) : Expr → Bool
  | .matchE src _ t =>
      (match src with
        | .var y => y == x
        | _ => false) || readsSpace x src || readsSpace x t
  | .ctor _ args => readsSpaceAll x args
  | .self args => readsSpaceAll x args
  | .prim _ args => readsSpaceAll x args
  | .call _ args => readsSpaceAll x args
  | .enter _ args => readsSpaceAll x args
  | .letE _ v b => readsSpace x v || readsSpace x b
  | .ifE c t e => readsSpace x c || readsSpace x t || readsSpace x e
  | .caseE k _ bs => readsSpace x k || readsSpaceAll x bs
  | .var _ => false
  | .const _ => false
  | .empty => false

def readsSpaceAll (x : String) : List Expr → Bool
  | [] => false
  | e :: es => readsSpace x e || readsSpaceAll x es
end

/-- Whether some equation's pattern at the parameter is a variable it reads as a
space. -/
def readsParam (eqs : List Equation) (i : ℕ) : Bool :=
  eqs.any fun eq => match eq.pats[i]? with
    | some (.var x) => readsSpace x eq.rhs
    | _ => false

/-- `contract_entry_facts`: an ANY parameter some equation reads as a space is a
space parameter; every other fact stays. -/
def classify (eqs : List Equation) (i : ℕ) : Pos → Pos
  | .any => if readsParam eqs i then .space else .any
  | p => p

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (decls decls_functional sym num str app noRes ops ops_mem plus_literal
  minus_literal greater_literal numEq_literal)
open TwoWayTypedVersions.Controls (number holds_num num_ground noEnter)

/-- `(= (reach $kb $n) (if (== $n 0) 0 (match $kb (edge $x) (reach $kb (- $n 1)))))` at
`(: reach (-> $s Number Number))`: the space parameter sits at a guarded formal, a type
variable named once. -/
def reachEq : Equation :=
  ⟨[.var "kb", .var "n"],
    .ifE (.prim "==" [.var "n", .const (num 0)]) (.const (num 0))
      (.matchE (.var "kb") (.ctor "edge" [.var "x"])
        (.self [.var "kb", .prim "-" [.var "n", .const (num 1)]]))⟩

/-- The C's classification gives the first parameter the space fact. -/
theorem reach_classified :
    classify [reachEq] 0 .any = .space ∧ classify [reachEq] 1 (.ground number) = .ground number := by
  decide

def reachProgram : TProgram := ⟨[.space, .ground number], .closed number, fun _ => none, primClass, []⟩

/-- **`reach` is accepted**: the `match` reads the space variable, its pattern is
uninterpreted, and the call to itself passes the space variable and a ground
`Number`. -/
theorem reach_accepted (grounded : String → Bool) : TAccepted decls grounded reachProgram reachEq := by
  refine ⟨rfl, _, _, .ifE (.prim (.cons (.var _ "n" none fun _ h => by cases h)
      (.cons (.const _ _ none fun _ h => by cases h) (.nil _))) rfl)
    (.const _ _ (some number) fun T h => ?_)
    (.matchVar (by simp [eqSpaces, reachProgram, reachEq]) (by decide +kernel)
      (.self (.cons (.var _ "kb" none fun _ h => by cases h)
        (.cons (.prim (.cons (.var _ "n" none fun _ h => by cases h)
          (.cons (.const _ _ none fun _ h => by cases h) (.nil _))) rfl) (.nil _)))
        (Or.inr (.cons ⟨"kb", rfl, by simp [eqSpaces, reachProgram, reachEq]⟩
          (.cons ⟨by decide +kernel, rfl⟩ .nil))))), Or.inr ⟨by decide +kernel, rfl⟩⟩
  cases h
  exact ⟨num_ground 0, holds_num grounded 0⟩

/-- `(edge a)` and `(edge b)`: two rows of the space `kb`. -/
def edges : Multiset Atom := {app "edge" [sym "a"], app "edge" [sym "b"]}

/-- The protocol's view: `kb` holds the two edges; no other space has rows. -/
def spaceEnv : Env := ⟨ops, fun _ _ => 0, fun w => if w = sym "kb" then edges else 0⟩

/-- The version's view: `kb` holds the same edges; another space holds a row the
protocol does not see. -/
def otherEnv : Env :=
  ⟨ops, fun _ _ => 0, fun w => if w = sym "kb" then edges else {app "edge" [sym "c"]}⟩

/-- The entry admits the space `kb`. -/
def kbOk (w : Atom) : Prop := w = sym "kb"

theorem reach_hyps (grounded : String → Bool) :
    TVersionHyps decls grounded kbOk reachProgram spaceEnv otherEnv [reachEq] noEnter noEnter where
  functional := decls_functional
  accepted eq member := by
    simp only [List.mem_singleton] at member
    subst member
    exact reach_accepted grounded
  enterAgree _ _ _ offered := by cases offered
  enterAnswers _ _ _ offered := by cases offered
  prim := (TypedCalls.Controls.env_ok (Γ := decls) grounded noRes).prim
  primSame := rfl
  keptSame := rfl
  rows w admitted := by
    subst admitted
    simp [spaceEnv, otherEnv]
  named _ member := by cases member

/-- `(-> $s Number Number)` reads alike `(-> %Undefined% Number Number)`. -/
theorem reach_erases :
    Erases (Ty.sym "Number") [.var "s", .sym "Number"]
      (([.sym "%Undefined%", number] : List (Ty Empty)).map Ty.lift) :=
  .step (pre := []) (post := [.sym "Number"]) (by simp) (by simp [Ty.vars]) (by simp [Ty.vars])
    (.refl _)

/-- **A space parameter at a guarded formal, read by `match`**: the protocol of
`(-> $s Number Number)` over the space as the protocol sees it is the version over the
space as the version sees it, at every fuel, multiplicity included, for every space
the entry admits; the views differ on every other space, which the version never
reads. -/
theorem reach_version (grounded : String → Bool) (n : ℕ) (k : ℤ) :
    protocolRun decls grounded (relBody spaceEnv noEnter [reachEq])
        (arrow [.var "s", .sym "Number"] (Ty.sym "Number")) n [sym "kb", num k] =
      versionRun (relBody otherEnv noEnter [reachEq]) n [sym "kb", num k] :=
  private_ground_version_eq_protocol (reach_hyps grounded) (As := [.sym "%Undefined%", number])
    (.cons (show demand ((Ty.sym "%Undefined%" : Ty Empty).lift : Ty String) ≠ .guarded by decide)
      (.cons ⟨rfl, by decide⟩ .nil)) ⟨rfl, by decide⟩ reach_erases n [sym "kb", num k]
    (.cons ⟨by simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars], rfl⟩
      (.cons ⟨num_ground k, holds_num grounded k⟩ .nil))

/-- `(reach kb 1)` answers `0` once per row of `kb`. -/
theorem reach_answers :
    versionRun (relBody otherEnv noEnter [reachEq]) 3 [sym "kb", num 1] = {num 0, num 0} := by
  cbv

/-- **A `match` over a space the entry does not admit is declined**: `other` is no space
parameter and no space the version names, so the analysis has no rule for it, and the
two views of the spaces give that `match` different rows. -/
theorem unadmitted_space_declined (grounded : String → Bool) (F F' : ContractBindingFacts.Facts)
    (v : TValue) :
    ¬ TAdmits decls grounded reachProgram (eqTypes decls reachProgram.positions reachEq.pats)
        (eqSpaces reachProgram.positions reachEq.pats) F
        (.matchE (.const (sym "other")) (.ctor "edge" [.var "x"]) (.var "x")) v F' ∧
      spaceEnv.rows (sym "other") ≠ otherEnv.rows (sym "other") := by
  refine ⟨fun admits => ?_, by simp [spaceEnv, otherEnv]⟩
  cases admits with
  | matchNamed named _ _ => simp [reachProgram] at named

/-! ### GROUND at a private formal -/

/-- `(= (len Nil) 0)` at `(: len (-> (List $a) Number))`. -/
def lenNil : Equation := ⟨[.const (sym "Nil")], .const (num 0)⟩

/-- `(= (len (Cons $x $xs)) (+ 1 (len $xs)))`. -/
def lenCons : Equation :=
  ⟨[.ctor "Cons" [.var "x", .var "xs"]], .prim "+" [.const (num 1), .self [.var "xs"]]⟩

/-- `len` read at the instance `τ` of its private formal. -/
def lenProgram (τ : String → Ty Empty) : TProgram :=
  ⟨[.ground (TypedCalls.Controls.listA.bind τ)], .closed number, fun _ => none, primClass, []⟩

/-- **`len` is accepted at every instance**: `$xs` is a list at the instance by the
constructor's declaration, so the call to itself meets the GROUND fact there. -/
theorem len_accepted (grounded : String → Bool) (τ : String → Ty Empty) :
    ∀ eq ∈ [lenNil, lenCons], TAccepted decls grounded (lenProgram τ) eq := by
  intro eq member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨rfl, _, _, .const _ _ (some number) (fun T h => by
      cases h
      exact ⟨num_ground 0, holds_num grounded 0⟩), Or.inr ⟨rfl, rfl⟩⟩
  · have factXs : eqTypes decls (lenProgram τ).positions lenCons.pats "xs"
        (TypedCalls.Controls.listA.bind τ) :=
      ⟨TypedCalls.Controls.listA.bind τ, .ctor "Cons" [.var "x", .var "xs"], by simp [lenProgram, lenCons],
        PatFact.ctor (σ := τ) (B := TypedCalls.Controls.listOf (.var "a")) (p := .var "xs")
          TypedCalls.Controls.cons_row TypedCalls.Controls.cons_constructor rfl
          (by simp [MetaName, TypedCalls.Controls.listA, TypedCalls.Controls.listOf])
          (by simp [Named, TypedCalls.Controls.listA, TypedCalls.Controls.listOf]) rfl (by simp)
          (by simp [FreeField, TypedCalls.Controls.listOf]) (PatFact.var _ _)⟩
    refine ⟨rfl, _, _, .prim (.cons (.const _ _ none fun _ h => by cases h)
        (.cons (.self (.cons (.var _ "xs" (some (TypedCalls.Controls.listA.bind τ)) fun _ h => by
          cases h
          exact factXs) (.nil _)) (Or.inr (.cons ⟨rfl, rfl⟩ .nil))) (.nil _))) rfl,
      Or.inr ⟨rfl, rfl⟩⟩

theorem len_hyps (grounded : String → Bool) (τ : String → Ty Empty) :
    TVersionHyps decls grounded (fun _ => False) (lenProgram τ) TypedCalls.Controls.env
      TypedCalls.Controls.env [lenNil, lenCons] noEnter noEnter where
  functional := decls_functional
  accepted := len_accepted grounded τ
  enterAgree _ _ _ offered := by cases offered
  enterAnswers _ _ _ offered := by cases offered
  prim := (TypedCalls.Controls.env_ok (Γ := decls) grounded noRes).prim
  primSame := rfl
  keptSame := rfl
  rows _ _ := rfl
  named _ member := by cases member

/-- **`len`'s version is the protocol of `(-> (List $a) Number)`** at every instance and
fuel, multiplicity included, at a ground list typed at the instance. -/
theorem len_version (grounded : String → Bool) (τ : String → Ty Empty) (n : ℕ) (ws : List Atom)
    (admitted : TAdmitted decls grounded (fun _ => False) (lenProgram τ).positions ws) :
    protocolRun decls grounded (relBody TypedCalls.Controls.env noEnter [lenNil, lenCons])
        (arrow [TypedCalls.Controls.listA] (Ty.sym "Number")) n ws =
      versionRun (relBody TypedCalls.Controls.env noEnter [lenNil, lenCons]) n ws :=
  private_formal_version_eq_protocol (len_hyps grounded τ) (Pre := []) (Post := []) (pre := [])
    (post := []) (R := .sym "Number") τ rfl rfl (by decide) (noMeta_app _) (by simp) (by simp)
    (by simp)
    (rowReduces_closed (As := [TypedCalls.Controls.listA.bind τ]) (R := number)
      (.cons ⟨rfl, by rw [demand_bind_lift (F := TypedCalls.Controls.listA) (fun y h => by cases h) τ]; decide⟩
        .nil) ⟨rfl, by decide⟩)
    n ws admitted

/-- `(Cons "s" Nil)` is a ground list of strings. -/
theorem strings_admitted (grounded : String → Bool) :
    TAdmitted decls grounded (fun _ => False) (lenProgram fun _ => .sym "String").positions
      [app "Cons" [str "s", sym "Nil"]] := by
  refine .cons ⟨Finset.eq_empty_iff_forall_notMem.mpr fun z occurs => ?_, Holds.of_count ?_⟩ .nil
  · obtain ⟨part, member, occurs⟩ := (support_expression _ z).mp occurs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
  · have := ctor_construction decls_functional TypedCalls.Controls.cons_row
      TypedCalls.Controls.cons_constructor [str "s", sym "Nil"] rfl (fun _ => .sym "String") (fun q member _ => by
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl
        · simpa using count_class decls (g := .string "s") (c := "String") rfl (.sym "String")
        · exact TypedCalls.Controls.count_nil _)
    simpa [TypedCalls.Controls.listA, TypedCalls.Controls.listOf] using this

/-- **The same version at another instance**: `(len (Cons "s" Nil))` answers `1` through
the protocol of `(-> (List $a) Number)`, as the version does at the instance
`$a := String`; `(len (Cons 1 (Cons 2 Nil)))` answers `2` in the same version. -/
theorem len_answers (grounded : String → Bool) :
    protocolRun decls grounded (relBody TypedCalls.Controls.env noEnter [lenNil, lenCons])
        (arrow [TypedCalls.Controls.listA] (Ty.sym "Number")) 3 [app "Cons" [str "s", sym "Nil"]] =
      {num 1} ∧
      versionRun (relBody TypedCalls.Controls.env noEnter [lenNil, lenCons]) 4
        [app "Cons" [num 1, app "Cons" [num 2, sym "Nil"]]] = {num 2} := by
  refine ⟨?_, by cbv⟩
  rw [len_version grounded (fun _ => .sym "String") 3 _ (strings_admitted grounded)]
  cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PrivateSpaceVersions
