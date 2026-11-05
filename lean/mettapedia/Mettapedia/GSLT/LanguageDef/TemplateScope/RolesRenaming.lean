import Mettapedia.GSLT.LanguageDef.TemplateScope.RolesLawsNecessity

/-!
# Binding by role: L1, L2 and L5

* `ann_mapN` — **L1, alpha-invariance**: for every signature, resolving a text
  whose spellings are renamed by an injective map is renaming the resolution.
  Owners are positions, so which binder an occurrence denotes does not depend on
  spellings.  `not_alpha_of_merge` — the injectivity is needed: merging two
  spellings lets a shadowing arrow capture an occurrence that denoted something
  else.
* `paste_at_hole` — **L2, pasting**: a fragment plugged into a context is
  resolved at the hole's binders and position, in an environment the context
  supplies, and the context's own resolution does not change (`context_stable`).
  `form_keeps_identities` — code formed from parts owns nothing: its names keep
  the identities they have where they are written.  `frame_owns` — a frame
  written whole owns them instead; the formed and written closures of the
  boundary study answer `(1 2)` and two unbound names.
* `row_uses_apart` — **L5, stable stored code**: a stored row is reusable code,
  so each use is a run of its frame and its names are private to the use
  (`private_inside`); `inline_rows_share` — written inline as an expression the
  same row shares its names between the two uses.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Roles

open Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v w

variable {C : Type w} {S : Type u} {X Y : Type v}

/-- Rename every spelling. -/
def RSrc.mapN (f : X → Y) : RSrc C S X → RSrc C S Y
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv (f y)
  | .par z => .par (f z)
  | .app a b => .app (mapN f a) (mapN f b)
  | .alt a b => .alt (mapN f a) (mapN f b)
  | .new ys b => .new (ys.map f) (mapN f b)
  | .frame z xs b => .frame (f z) (xs.map (List.map f)) (mapN f b)
  | .form z b => .form (f z) (mapN f b)
  | .pat c p w b xs => .pat c (mapN f p) (mapN f w) (mapN f b) (xs.map (List.map f))
  | .quote c => .quote (mapN f c)
  | .pquote c => .pquote (mapN f c)

namespace RSrc

theorem patNames_mapN (f : X → Y) : ∀ p : RSrc C S X, (mapN f p).patNames = p.patNames.map f
  | .sv _ => rfl
  | .app a b => by simp [mapN, patNames, patNames_mapN f a, patNames_mapN f b]
  | .sym _ => rfl
  | .fn _ => rfl
  | .par _ => rfl
  | .alt _ _ => rfl
  | .new _ _ => rfl
  | .frame _ _ _ => rfl
  | .form _ _ => rfl
  | .pat _ _ _ _ _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl

theorem dir_mapN (σ : Signature C) (f : X → Y) : ∀ t : RSrc C S X, (mapN f t).dir σ = (t.dir σ).map f
  | .sv _ => rfl
  | .app a b => by simp [mapN, dir, dir_mapN σ f a, dir_mapN σ f b]
  | .alt a b => by simp [mapN, dir, dir_mapN σ f a, dir_mapN σ f b]
  | .new _ b => by simp [mapN, dir, dir_mapN σ f b]
  | .form _ b => by simp [mapN, dir, dir_mapN σ f b]
  | .pat c p w b _ => by
      simp only [mapN, dir, dir_mapN σ f p, dir_mapN σ f w, dir_mapN σ f b]
      cases σ.order c <;> simp
  | .quote c => by simp [mapN, dir, dir_mapN σ f c]
  | .pquote c => by simp [mapN, dir, dir_mapN σ f c]
  | .sym _ => rfl
  | .fn _ => rfl
  | .par _ => rfl
  | .frame _ _ _ => rfl

theorem crs_mapN (f : X → Y) : ∀ t : RSrc C S X, (mapN f t).crs = t.crs.map f
  | .app a b => by simp [mapN, crs, crs_mapN f a, crs_mapN f b]
  | .alt a b => by simp [mapN, crs, crs_mapN f a, crs_mapN f b]
  | .new _ b => by simp [mapN, crs, crs_mapN f b]
  | .frame _ xs _ => by cases xs <;> simp [mapN, crs]
  | .form _ b => by simp [mapN, crs, crs_mapN f b]
  | .pat _ p w b xs => by
      cases xs <;> simp [mapN, crs, crs_mapN f p, crs_mapN f w, crs_mapN f b]
  | .quote c => by simp [mapN, crs, crs_mapN f c]
  | .pquote c => by simp [mapN, crs, crs_mapN f c]
  | .sv _ => rfl
  | .sym _ => rfl
  | .fn _ => rfl
  | .par _ => rfl

theorem relUses_mapN (σ : Signature C) (f : X → Y) :
    ∀ t : RSrc C S X, (mapN f t).relUses σ = (t.relUses σ).map f
  | .app a b => by simp [mapN, relUses, relUses_mapN σ f a, relUses_mapN σ f b]
  | .alt a b => by simp [mapN, relUses, relUses_mapN σ f a, relUses_mapN σ f b]
  | .new _ b => by simp [mapN, relUses, relUses_mapN σ f b]
  | .form _ b => by simp [mapN, relUses, relUses_mapN σ f b]
  | .pat c p w b xs => by
      cases xs with
      | none =>
          by_cases h : σ.role c = .rel <;>
            simp [mapN, relUses, h, patNames_mapN, relUses_mapN σ f w, relUses_mapN σ f b]
      | some _ => simp [mapN, relUses, relUses_mapN σ f w, relUses_mapN σ f b]
  | .quote c => by simp [mapN, relUses, relUses_mapN σ f c]
  | .pquote c => by simp [mapN, relUses, relUses_mapN σ f c]
  | .sv _ => rfl
  | .sym _ => rfl
  | .fn _ => rfl
  | .par _ => rfl
  | .frame _ _ _ => rfl

end RSrc

variable [DecidableEq X] [DecidableEq Y]

omit [DecidableEq X] [DecidableEq Y] in
/-- Filtering a renamed list by a renamed predicate is renaming the filtered
list. -/
theorem filter_map_transport (f : X → Y) (l : List X) (p : Y → Bool) (q : X → Bool)
    (h : ∀ x ∈ l, p (f x) = q x) : (l.map f).filter p = (l.filter q).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha := h a (List.mem_cons_self ..)
      have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.filter_cons, ha]
      split <;> simp [ih']

theorem without_mapN {f : X → Y} (hf : Function.Injective f) (R ys : List X) :
    without (R.map f) (ys.map f) = (without R ys).map f := by
  unfold without
  exact filter_map_transport f R _ _ (fun x _ => by simp [List.mem_map_of_injective hf])

theorem own_mapN (σ : Signature C) {f : X → Y} (hf : Function.Injective f) (B : List X)
    (b : RSrc C S X) : own σ (B.map f) (b.mapN f) = (own σ B b).map f := by
  unfold own
  cases σ.frame with
  | lexical => rfl
  | relNames =>
      simp only [RSrc.relUses_mapN]
      rw [filter_map_transport f _ _ (fun y => decide (y ∉ B))
        (fun x _ => by simp [List.mem_map_of_injective hf]), List.dedup_map_of_injective hf]
  | clause =>
      simp only [RSrc.dir_mapN, RSrc.crs_mapN]
      have hd : ((((b.dir σ).map f).filter fun y => decide (y ∉ B.map f))).dedup =
          (((b.dir σ).filter fun y => decide (y ∉ B)).dedup).map f := by
        rw [filter_map_transport f _ _ (fun y => decide (y ∉ B))
          (fun x _ => by simp [List.mem_map_of_injective hf]), List.dedup_map_of_injective hf]
      rw [hd, filter_map_transport f _ _
        (fun y => decide (y ∉ B ∧ y ∉ (((b.dir σ).filter fun y => decide (y ∉ B)).dedup)))
        (fun x _ => by simp [List.mem_map_of_injective hf]), List.dedup_map_of_injective hf,
        List.map_append]

theorem bodyB_mapN (σ : Signature C) {f : X → Y} (hf : Function.Injective f) (B : List X)
    (b : RSrc C S X) : bodyB σ (B.map f) (b.mapN f) = (bodyB σ B b).map f := by
  unfold bodyB
  split <;> simp [own_mapN σ hf]

theorem intro_mapN (σ : Signature C) {f : X → Y} (hf : Function.Injective f) (B R : List X)
    (c : C) (p : RSrc C S X) (xs : Option (List X)) :
    intro σ (B.map f) (R.map f) c (p.mapN f) (xs.map (List.map f)) = (intro σ B R c p xs).map f := by
  unfold intro
  cases xs with
  | some sh =>
      simp only [Option.map_some, RSrc.patNames_mapN]
      rw [filter_map_transport f _ _ (fun y => decide (y ∉ sh))
        (fun x _ => by simp [List.mem_map_of_injective hf]), List.dedup_map_of_injective hf]
  | none =>
      simp only [Option.map_none, RSrc.patNames_mapN]
      cases σ.role c with
      | rel => rfl
      | arrow m =>
          cases m with
          | shadow =>
              simp only
              rw [filter_map_transport f _ _ (fun y => decide (y ∉ R))
                (fun x _ => by simp [List.mem_map_of_injective hf]),
                List.dedup_map_of_injective hf]
          | test =>
              simp only
              rw [filter_map_transport f _ _ (fun y => decide (y ∉ B))
                (fun x _ => by simp [List.mem_map_of_injective hf]),
                List.dedup_map_of_injective hf]

omit [DecidableEq X] [DecidableEq Y] in
theorem patB_mapN (f : X → Y) (B : List X) (p : RSrc C S X) (xs : Option (List X)) :
    patB (B.map f) (p.mapN f) (xs.map (List.map f)) = (patB B p xs).map f := by
  cases xs <;> simp [patB, RSrc.patNames_mapN]

theorem patR_mapN {f : X → Y} (hf : Function.Injective f) (R I : List X) (xs : Option (List X)) :
    patR (R.map f) (xs.map (List.map f)) (I.map f) = (patR R xs I).map f := by
  cases xs <;> simp [patR, without_mapN hf]

/-- Renaming commutes with the names a resolution reads. -/
theorem cons_mapN (σ : Signature C) {f : X → Y} (hf : Function.Injective f) :
    ∀ (t : RSrc C S X) (B R : List X), cons σ (B.map f) (R.map f) (t.mapN f) = (cons σ B R t).map f
  | .sym _, _, _ => rfl
  | .fn _, _, _ => rfl
  | .sv _, _, _ => rfl
  | .par _, _, _ => rfl
  | .app a b, B, R => by
      simp [RSrc.mapN, cons, cons_mapN σ hf a, cons_mapN σ hf b]
  | .alt a b, B, R => by
      simp [RSrc.mapN, cons, cons_mapN σ hf a, cons_mapN σ hf b]
  | .new ys b, B, R => by
      simp only [RSrc.mapN, cons]
      rw [← List.map_append, without_mapN hf, cons_mapN σ hf b]
      exact filter_map_transport f _ _ _ (fun x _ => by simp [List.mem_map_of_injective hf])
  | .frame z none b, B, R => by
      simp only [RSrc.mapN, Option.map_none, cons]
      rw [own_mapN σ hf, bodyB_mapN σ hf, without_mapN hf, cons_mapN σ hf b]
      exact filter_map_transport f _ _ _ (fun x _ => by simp [List.mem_map_of_injective hf])
  | .frame z (some sh) b, B, R => by
      simp only [RSrc.mapN, Option.map_some, cons]
      rw [← List.map_append, cons_mapN σ hf b, List.map_append]
      congr 1
      exact filter_map_transport f _ _ _ (fun x _ => by simp [List.mem_map_of_injective hf])
  | .form z b, B, R => by
      simp [RSrc.mapN, cons, cons_mapN σ hf b]
  | .pat c p w b xs, B, R => by
      simp only [RSrc.mapN, cons]
      rw [intro_mapN σ hf, patR_mapN hf, patB_mapN, cons_mapN σ hf p, cons_mapN σ hf b,
        cons_mapN σ hf w, ← List.map_append,
        filter_map_transport f _ _ (fun y => decide (y ∉ intro σ B R c p xs))
          (fun x _ => by simp [List.mem_map_of_injective hf])]
      cases xs <;> simp
  | .quote c, B, R => by simp [RSrc.mapN, cons, cons_mapN σ hf c]
  | .pquote c, B, R => by simp [RSrc.mapN, cons, cons_mapN σ hf c]

theorem sealOwn_mapN (σ : Signature C) {f : X → Y} (hf : Function.Injective f) (B sh : List X)
    (b : RSrc C S X) : sealOwn σ (B.map f) (sh.map f) (b.mapN f) = (sealOwn σ B sh b).map f := by
  unfold sealOwn
  rw [← List.map_append, cons_mapN σ hf b,
    filter_map_transport f _ _ (fun y => decide (y ∉ sh))
      (fun x _ => by simp [List.mem_map_of_injective hf]), List.dedup_map_of_injective hf]

theorem update_mapN {f : X → Y} (hf : Function.Injective f) {E : REnv X} {E' : REnv Y}
    (hE : ∀ y, E' (f y) = E y) (ys : List X) (o : Owner) :
    ∀ y, (E'.update (ys.map f) o) (f y) = (E.update ys o) y := by
  intro y
  by_cases hy : y ∈ ys
  · rw [update_mem hy, update_mem ((List.mem_map_of_injective hf).2 hy)]
  · rw [update_not_mem hy, update_not_mem (fun h => hy ((List.mem_map_of_injective hf).1 h)),
      hE]

/-- **L1, alpha-invariance.**  For every signature, renaming the spellings of a
text by an injective map renames its resolution and changes no owner. -/
theorem ann_mapN (σ : Signature C) {f : X → Y} (hf : Function.Injective f) :
    ∀ (t : RSrc C S X) (E : REnv X) (E' : REnv Y) (B R : List X) (π : Owner),
      (∀ y, E' (f y) = E y) →
      ann σ E' (B.map f) (R.map f) π (t.mapN f) = (ann σ E B R π t).mapN (Prod.map id f)
  | .sym _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _ => rfl
  | .sv y, E, E', B, R, π, hE => by simp [RSrc.mapN, ann, hE]
  | .par _, _, _, _, _, _, _ => rfl
  | .app a b, E, E', B, R, π, hE => by
      simp [RSrc.mapN, ann, ann_mapN σ hf a E E' B R _ hE, ann_mapN σ hf b E E' B R _ hE]
  | .alt a b, E, E', B, R, π, hE => by
      simp [RSrc.mapN, ann, ann_mapN σ hf a E E' B R _ hE, ann_mapN σ hf b E E' B R _ hE]
  | .new ys b, E, E', B, R, π, hE => by
      simp only [RSrc.mapN, ann]
      rw [← List.map_append, without_mapN hf,
        ann_mapN σ hf b _ _ _ _ _ (update_mapN hf hE ys π)]
      simp [List.map_map, Function.comp_def]
  | .frame z none b, E, E', B, R, π, hE => by
      simp only [RSrc.mapN, Option.map_none, ann]
      rw [own_mapN σ hf, bodyB_mapN σ hf, without_mapN hf,
        ann_mapN σ hf b _ _ _ _ _ (update_mapN hf hE _ π)]
      rfl
  | .frame z (some sh) b, E, E', B, R, π, hE => by
      simp only [RSrc.mapN, Option.map_some, ann]
      rw [sealOwn_mapN σ hf, ← List.map_append,
        ann_mapN σ hf b _ _ _ _ _ (update_mapN hf hE _ π)]
      simp [List.map_map, Function.comp_def, hE]
  | .form z b, E, E', B, R, π, hE => by
      simp only [RSrc.mapN, ann]
      rw [ann_mapN σ hf b E E' B R _ hE]
      rfl
  | .pat c p w b xs, E, E', B, R, π, hE => by
      simp only [RSrc.mapN, ann]
      rw [intro_mapN σ hf, patR_mapN hf, patB_mapN,
        ann_mapN σ hf p _ _ _ _ _ (update_mapN hf hE _ π),
        ann_mapN σ hf w E E' B R _ hE,
        ann_mapN σ hf b _ _ _ _ _ (update_mapN hf hE _ π)]
      cases xs <;> simp [List.map_map, Function.comp_def, hE]
  | .quote c, E, E', B, R, π, hE => by
      simp only [RSrc.mapN, ann]
      rw [ann_mapN σ hf c E E' B R _ hE]
  | .pquote c, E, E', B, R, π, hE => by
      simp only [RSrc.mapN, ann]
      rw [ann_mapN σ hf c E E' B R _ hE]

/-- **Injectivity is needed for L1.**  Merging two spellings lets a shadowing
arrow capture an occurrence that denoted an unknown outside it. -/
theorem not_alpha_of_merge (σ : Signature C) (c : C) (hc : σ.role c = .arrow .shadow) {x y : X}
    (hxy : x ≠ y) :
    ann σ (fun _ => [9]) [] [] []
        ((RSrc.pat c (.sv x) (.par x) (.sv y) none : RSrc C S X).mapN fun _ => x) ≠
      (ann σ (fun _ => [9]) [] [] [] (RSrc.pat c (.sv x) (.par x) (.sv y) none)).mapN
        (Prod.map id fun _ => x) := by
  have h1 : intro σ [] [] c (RSrc.sv x : RSrc C S X) none = [x] := by
    simp [intro, hc, RSrc.patNames]
  simp [RSrc.mapN, ann, h1, REnv.update, hxy.symm]

/-! ## L2: pasting and built code -/

/-- **L2, pasting.**  A fragment plugged into a context is resolved at the
hole's binders, crossing names and position, in the environment the context
supplies there, and the context's frames do not depend on it. -/
theorem paste_at_hole {σ : Signature C} (hs : Stable σ) (K : List (RFrame C S X)) (E : REnv X)
    (B R : List X) (hRB : ∀ y ∈ R, y ∈ B) (π : Owner) (t : RSrc C S X) :
    ∃ (K' : List (RFrame C S (Owner × X))) (Eh : REnv X),
      split K (ann σ E B R π (RFrame.plugAll K t)) =
        some (K', ann σ Eh (RFrame.holeB B K) (holeR σ B R K) (RFrame.holePos π K) t) := by
  obtain ⟨K', Eh, _, h1, _⟩ := context_stable hs K E E B R π t t hRB (fun _ _ => rfl)
  exact ⟨K', Eh, h1⟩

/-- **Built code keeps identities**: a lambda formed from parts owns nothing;
its body's names denote what they denote where the parts were written. -/
theorem form_keeps_identities (σ : Signature C) (E : REnv X) (B R : List X) (π : Owner) (z : X)
    (b : RSrc C S X) : ann σ E B R π (.form z b) = .form (π, z) (ann σ E B R (π ++ [0]) b) :=
  rfl

/-- A frame written whole owns the names written at its level that no binder
on its path introduced, under the clause policy. -/
theorem frame_owns {σ : Signature C} (hσ : σ.frame = .clause) (E : REnv X) (B R : List X)
    (π : Owner) (z y : X) (hB : y ∉ B) :
    ann σ E B R π (.frame z none (.sv y : RSrc C S X)) =
      .frame (π, z) none (.sv (π, y)) := by
  have hown : y ∈ own σ B (RSrc.sv y : RSrc C S X) :=
    (mem_own_clause hσ).2 ⟨hB, by simp [uses, RSrc.dir]⟩
  simp [ann, update_mem hown]

/-! ## L5: stored rows -/

/-- **L5, stable stored code.**  Two uses of a stored row, each a run of the
row's frame, resolve the row's name to their own runs. -/
theorem row_uses_apart {σ : Signature C} (hσ : σ.frame = .clause) (E : REnv X) (π : Owner)
    (u z : X) :
    ann σ E [] [] π (.app (.frame u none (.sv z)) (.frame u none (.sv z)) : RSrc C S X) =
      .app (.frame (π ++ [0], u) none (.sv (π ++ [0], z)))
        (.frame (π ++ [1], u) none (.sv (π ++ [1], z))) := by
  rw [show ann σ E [] [] π (.app (.frame u none (.sv z)) (.frame u none (.sv z)) : RSrc C S X) =
      .app (ann σ E [] [] (π ++ [0]) (.frame u none (.sv z)))
        (ann σ E [] [] (π ++ [1]) (.frame u none (.sv z))) from rfl,
    frame_owns hσ E [] [] (π ++ [0]) u z List.not_mem_nil,
    frame_owns hσ E [] [] (π ++ [1]) u z List.not_mem_nil]

/-- **Inline rows share.**  The same row written as an expression twice in one
frame is one unknown: reading it binds it for the other read. -/
theorem inline_rows_share (σ : Signature C) (E : REnv X) (B R : List X) (π : Owner) (z : X) :
    ann σ E B R π (.app (.sv z) (.sv z) : RSrc C S X) = .app (.sv (E z, z)) (.sv (E z, z)) :=
  rfl

/-! ## Binder-local renaming -/

/-- Every spelling written in a text: names, parameters, binders, crossing
sets. -/
def RSrc.names : RSrc C S X → List X
  | .sv y => [y]
  | .par z => [z]
  | .app a b => names a ++ names b
  | .alt a b => names a ++ names b
  | .new ys b => ys ++ names b
  | .frame z xs b => z :: (xs.getD [] ++ names b)
  | .form z b => z :: names b
  | .pat _ p w b xs => names p ++ names w ++ names b ++ xs.getD []
  | .quote c => names c
  | .pquote c => names c
  | _ => []

/-- A resolution reads only names written in the text. -/
theorem cons_sub_names (σ : Signature C) :
    ∀ (t : RSrc C S X) (B R : List X), ∀ y ∈ cons σ B R t, y ∈ t.names
  | .sym _, _, _, y, h => by simp [cons] at h
  | .fn _, _, _, y, h => by simp [cons] at h
  | .sv _, _, _, y, h => by simpa [cons, RSrc.names] using h
  | .par _, _, _, y, h => by simp [cons] at h
  | .app a b, B, R, y, h => by
      simp only [cons, List.mem_append] at h
      simp only [RSrc.names, List.mem_append]
      rcases h with h | h
      · exact Or.inl (cons_sub_names σ a B R y h)
      · exact Or.inr (cons_sub_names σ b B R y h)
  | .alt a b, B, R, y, h => by
      simp only [cons, List.mem_append] at h
      simp only [RSrc.names, List.mem_append]
      rcases h with h | h
      · exact Or.inl (cons_sub_names σ a B R y h)
      · exact Or.inr (cons_sub_names σ b B R y h)
  | .new ys b, B, R, y, h => by
      simp only [cons, List.mem_filter] at h
      simp only [RSrc.names, List.mem_append]
      exact Or.inr (cons_sub_names σ b _ _ y h.1)
  | .frame z none b, B, R, y, h => by
      simp only [cons, List.mem_filter] at h
      simp only [RSrc.names, Option.getD_none, List.nil_append, List.mem_cons]
      exact Or.inr (cons_sub_names σ b _ _ y h.1)
  | .frame z (some sh) b, B, R, y, h => by
      simp only [cons, List.mem_append, List.mem_filter] at h
      simp only [RSrc.names, Option.getD_some, List.mem_cons, List.mem_append]
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (cons_sub_names σ b _ _ y h.1))
  | .form z b, B, R, y, h => by
      simp only [cons] at h
      simp only [RSrc.names, List.mem_cons]
      exact Or.inr (cons_sub_names σ b B R y h)
  | .pat c p w b xs, B, R, y, h => by
      simp only [cons, List.mem_append, List.mem_filter] at h
      simp only [RSrc.names, List.mem_append]
      rcases h with ((⟨h | h, _⟩) | h) | h
      · exact Or.inl (Or.inl (Or.inl (cons_sub_names σ p _ _ y h)))
      · exact Or.inl (Or.inr (cons_sub_names σ b _ _ y h))
      · exact Or.inl (Or.inl (Or.inr (cons_sub_names σ w B R y h)))
      · exact Or.inr h
  | .quote c, B, R, y, h => by
      simp only [cons] at h
      exact cons_sub_names σ c B R y h
  | .pquote c, B, R, y, h => by
      simp only [cons] at h
      exact cons_sub_names σ c B R y h

omit [DecidableEq Y] in
theorem map_swap_of_not_mem {y y' : X} {l : List X} (h : y ∉ l) (h' : y' ∉ l) :
    l.map (Equiv.swap y y') = l := by
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro u hu
  exact Equiv.swap_apply_of_ne_of_ne (fun e => h (e ▸ hu)) (fun e => h' (e ▸ hu))

omit [DecidableEq Y] in
/-- **Binder-local renaming.**  If a fragment does not read `$y` from outside
(every occurrence of `$y` in it is bound inside it), renaming `$y` to a name
`$y'` written nowhere in it changes no owner: the resolution of the renamed
fragment is the renamed resolution.  With `context_stable`, the context around
the fragment does not change either. -/
theorem alpha_local (σ : Signature C) (t : RSrc C S X) (E : REnv X) (B R : List X) (π : Owner)
    {y y' : X} (hy : y ∉ cons σ B R t) (hy' : y' ∉ t.names) (hB : y ∉ B) (hB' : y' ∉ B)
    (hR : y ∉ R) (hR' : y' ∉ R) :
    ann σ E B R π (t.mapN (Equiv.swap y y')) =
      (ann σ E B R π t).mapN (Prod.map id (Equiv.swap y y')) := by
  have hinj : Function.Injective (Equiv.swap y y') := (Equiv.swap y y').injective
  have h1 := ann_mapN σ hinj t E (E ∘ Equiv.swap y y') B R π
    (fun z => by simp [Function.comp, Equiv.swap_apply_self])
  rw [map_swap_of_not_mem hB hB', map_swap_of_not_mem hR hR'] at h1
  rw [← h1]
  apply ann_congr
  intro w hw
  have hc := cons_mapN σ hinj t B R
  rw [map_swap_of_not_mem hB hB', map_swap_of_not_mem hR hR'] at hc
  rw [hc] at hw
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
  have huy : u ≠ y := fun e => hy (e ▸ hu)
  have huy' : u ≠ y' := fun e => hy' (e ▸ cons_sub_names σ t B R u hu)
  simp [Function.comp, Equiv.swap_apply_of_ne_of_ne huy huy']

end Mettapedia.GSLT.LanguageDef.TemplateScope.Roles
