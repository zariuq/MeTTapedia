import Mettapedia.GSLT.LanguageDef.TemplateScope.Roles

/-!
# Binding by role: the laws, once

Theorems about the resolution `ann` of `TemplateScope.Roles`, for every
signature that meets the stated conditions.

* `ann_congr` — **locality**: the resolution of a fragment reads its
  environment only at the names `cons` lists.
* `cons_sub` — under the clause policy a fragment reads from outside only the
  names written at its own level and the names binders on its path introduced.
* `context_stable` — **L4, context stability**: for every signature whose frame
  policy is lexical or clause and which has no implicit nested capture, plugging
  any fragment into a context leaves the resolution of the context unchanged,
  and the fragment is resolved in the environment at the hole.
* `private_inside` — **L3, independent calls**: under the clause policy every
  occurrence inside a frame whose spelling no binder on the frame's path
  introduced resolves to the frame or to something inside it, so each run of
  the frame has its own copy.
* `relation_occ_frame` — **L6, one unknown per name per frame**: relation and
  expression occurrences reached without crossing an introducing binder resolve
  to one owner, the frame's.

The counterexamples showing that each condition is needed are in
`TemplateScope.RolesLawsNecessity`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Roles

open Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v w

variable {C : Type w} {S : Type u} {X : Type v} [DecidableEq X]

/-! ## Environment updates -/

theorem update_mem {E : REnv X} {ys : List X} {o : Owner} {y : X} (h : y ∈ ys) :
    E.update ys o y = o := by
  simp [REnv.update, h]

theorem update_not_mem {E : REnv X} {ys : List X} {o : Owner} {y : X} (h : y ∉ ys) :
    E.update ys o y = E y := by
  simp [REnv.update, h]

/-- Two environments agreeing outside `ys` agree everywhere after `ys` is
pointed at one owner. -/
theorem update_agree {E E' : REnv X} {ys L : List X} {o : Owner}
    (h : ∀ y ∈ L, y ∉ ys → E y = E' y) : ∀ y ∈ L, E.update ys o y = E'.update ys o y := by
  intro y hy
  by_cases hm : y ∈ ys
  · rw [update_mem hm, update_mem hm]
  · rw [update_not_mem hm, update_not_mem hm]
    exact h y hy hm

/-! ## Locality of the resolution -/

/-- **Locality.**  Two environments that agree on the names a fragment reads
resolve it alike. -/
theorem ann_congr (σ : Signature C) :
    ∀ (t : RSrc C S X) (E E' : REnv X) (B R : List X) (π : Owner),
      (∀ y ∈ cons σ B R t, E y = E' y) → ann σ E B R π t = ann σ E' B R π t
  | .sym _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _ => rfl
  | .sv y, E, E', B, R, π, h => by
      simp only [ann]
      rw [h y (by simp [cons])]
  | .par _, _, _, _, _, _, _ => rfl
  | .app f a, E, E', B, R, π, h => by
      simp only [ann]
      rw [ann_congr σ f E E' B R _ (fun y hy => h y (by simp [cons, hy])),
        ann_congr σ a E E' B R _ (fun y hy => h y (by simp [cons, hy]))]
  | .alt t₁ t₂, E, E', B, R, π, h => by
      simp only [ann]
      rw [ann_congr σ t₁ E E' B R _ (fun y hy => h y (by simp [cons, hy])),
        ann_congr σ t₂ E E' B R _ (fun y hy => h y (by simp [cons, hy]))]
  | .new ys b, E, E', B, R, π, h => by
      simp only [ann]
      rw [ann_congr σ b _ _ _ _ _ (update_agree (fun y hy hn => h y (by simp [cons, hy, hn])))]
  | .frame z none b, E, E', B, R, π, h => by
      simp only [ann]
      rw [ann_congr σ b _ _ _ _ _ (update_agree (fun y hy hn => h y (by simp [cons, hy, hn])))]
  | .frame z (some sh) b, E, E', B, R, π, h => by
      have hsh : ∀ y ∈ sh, E y = E' y := fun y hy => h y (by simp [cons, hy])
      have hb : ∀ y ∈ cons σ (B ++ sh) sh b, y ∉ sealOwn σ B sh b → E y = E' y := by
        intro y hy hn
        apply hsh
        by_contra hsy
        exact hn (by simp [sealOwn, hy, hsy])
      simp only [ann]
      rw [ann_congr σ b _ _ _ _ _ (update_agree hb)]
      congr 2
      exact List.map_congr_left (fun y hy => by rw [hsh y hy])
  | .form z b, E, E', B, R, π, h => by
      simp only [ann]
      rw [ann_congr σ b E E' B R _ (fun y hy => h y (by simp [cons, hy]))]
  | .pat c p w b xs, E, E', B, R, π, h => by
      have hp : ∀ y ∈ cons σ B (patR R xs (intro σ B R c p xs)) p, y ∉ intro σ B R c p xs →
          E y = E' y :=
        fun y hy hn => h y (by simp [cons, hy, hn])
      have hb : ∀ y ∈ cons σ (patB B p xs) (patR R xs (intro σ B R c p xs)) b,
          y ∉ intro σ B R c p xs → E y = E' y :=
        fun y hy hn => h y (by simp [cons, hy, hn])
      have hw : ∀ y ∈ cons σ B R w, E y = E' y := fun y hy => h y (by simp [cons, hy])
      have hx : ∀ y ∈ xs.getD [], E y = E' y := fun y hy => h y (by simp [cons, hy])
      simp only [ann]
      rw [ann_congr σ p _ _ _ _ _ (update_agree hp), ann_congr σ b _ _ _ _ _ (update_agree hb),
        ann_congr σ w E E' B R _ hw]
      congr 1
      cases xs with
      | none => rfl
      | some sh =>
          simp only [Option.map_some, Option.some.injEq]
          exact List.map_congr_left (fun y hy => by rw [hx y (by simpa using hy)])
  | .quote c, E, E', B, R, π, h => by
      simp only [ann]
      rw [ann_congr σ c E E' B R _ (fun y hy => h y (by simp [cons, hy]))]
  | .pquote c, E, E', B, R, π, h => by
      simp only [ann]
      rw [ann_congr σ c E E' B R _ (fun y hy => h y (by simp [cons, hy]))]

/-! ## What a clause frame owns -/

/-- The names written at a frame level, crossing sets included. -/
def uses (σ : Signature C) (t : RSrc C S X) : List X := t.dir σ ++ t.crs

theorem mem_own_clause {σ : Signature C} (hσ : σ.frame = .clause) {B : List X}
    {b : RSrc C S X} {y : X} : y ∈ own σ B b ↔ y ∉ B ∧ y ∈ uses σ b := by
  simp only [own, hσ, uses, List.mem_append, List.mem_dedup, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, _⟩)
    · exact ⟨h2, Or.inl h1⟩
    · exact ⟨h2, Or.inr h1⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · by_cases hd : y ∈ b.dir σ
      · exact Or.inl ⟨hd, h1⟩
      · exact Or.inr ⟨h2, h1, fun h => hd h.1⟩

theorem own_lexical {σ : Signature C} (hσ : σ.frame = .lexical) (B : List X) (b : RSrc C S X) :
    own σ B b = [] := by
  simp [own, hσ]

omit [DecidableEq X] in
/-- A pattern's names are written at its level. -/
theorem patNames_sub_dir (σ : Signature C) :
    ∀ (p : RSrc C S X), ∀ y ∈ p.patNames, y ∈ p.dir σ
  | .sv _, y, h => by simpa [RSrc.patNames, RSrc.dir] using h
  | .app f a, y, h => by
      simp only [RSrc.patNames, List.mem_append] at h
      simp only [RSrc.dir, List.mem_append]
      rcases h with h | h
      · exact Or.inl (patNames_sub_dir σ f y h)
      · exact Or.inr (patNames_sub_dir σ a y h)
  | .sym _, y, h => by simp [RSrc.patNames] at h
  | .fn _, y, h => by simp [RSrc.patNames] at h
  | .par _, y, h => by simp [RSrc.patNames] at h
  | .alt _ _, y, h => by simp [RSrc.patNames] at h
  | .new _ _, y, h => by simp [RSrc.patNames] at h
  | .frame _ _ _, y, h => by simp [RSrc.patNames] at h
  | .form _ _, y, h => by simp [RSrc.patNames] at h
  | .pat _ _ _ _ _, y, h => by simp [RSrc.patNames] at h
  | .quote _, y, h => by simp [RSrc.patNames] at h
  | .pquote _, y, h => by simp [RSrc.patNames] at h

omit [DecidableEq X] in
theorem mem_dir_pat (σ : Signature C) (c : C) (p w b : RSrc C S X) (xs : Option (List X))
    (y : X) : y ∈ (RSrc.pat c p w b xs).dir σ ↔ y ∈ p.dir σ ∨ y ∈ w.dir σ ∨ y ∈ b.dir σ := by
  simp only [RSrc.dir]
  cases σ.order c <;> simp [or_left_comm]

/-- **A clause fragment reads from outside only its own level and the binders
on its path.** -/
theorem cons_sub {σ : Signature C} (hσ : σ.frame = .clause) :
    ∀ (t : RSrc C S X) (B R : List X), ∀ y ∈ cons σ B R t, y ∈ uses σ t ∨ y ∈ B
  | .sym _, _, _, y, h => by simp [cons] at h
  | .fn _, _, _, y, h => by simp [cons] at h
  | .sv _, _, _, y, h => by simp_all [cons, uses, RSrc.dir]
  | .par _, _, _, y, h => by simp [cons] at h
  | .app f a, B, R, y, h => by
      simp only [cons, List.mem_append] at h
      simp only [uses, RSrc.dir, RSrc.crs, List.mem_append]
      rcases h with h | h
      · rcases cons_sub hσ f B R y h with h' | h'
        · simp only [uses, List.mem_append] at h'
          tauto
        · exact Or.inr h'
      · rcases cons_sub hσ a B R y h with h' | h'
        · simp only [uses, List.mem_append] at h'
          tauto
        · exact Or.inr h'
  | .alt t₁ t₂, B, R, y, h => by
      simp only [cons, List.mem_append] at h
      simp only [uses, RSrc.dir, RSrc.crs, List.mem_append]
      rcases h with h | h
      · rcases cons_sub hσ t₁ B R y h with h' | h'
        · simp only [uses, List.mem_append] at h'
          tauto
        · exact Or.inr h'
      · rcases cons_sub hσ t₂ B R y h with h' | h'
        · simp only [uses, List.mem_append] at h'
          tauto
        · exact Or.inr h'
  | .new ys b, B, R, y, h => by
      simp only [cons, List.mem_filter, decide_eq_true_eq] at h
      rcases cons_sub hσ b (B ++ ys) _ y h.1 with h' | h'
      · left
        simpa [uses, RSrc.dir, RSrc.crs] using h'
      · simp only [List.mem_append] at h'
        rcases h' with h' | h'
        · exact Or.inr h'
        · exact absurd h' h.2
  | .frame z none b, B, R, y, h => by
      simp only [cons, List.mem_filter, decide_eq_true_eq] at h
      right
      obtain ⟨hy, hn⟩ := h
      rw [mem_own_clause hσ] at hn
      unfold bodyB at hy
      split at hy
      · rcases cons_sub hσ b _ _ y hy with h' | h'
        · by_contra hB
          exact hn ⟨hB, h'⟩
        · simp only [List.mem_append] at h'
          rcases h' with h' | h'
          · exact h'
          · rw [mem_own_clause hσ] at h'
            exact absurd h' hn
      · rcases cons_sub hσ b _ _ y hy with h' | h'
        · by_contra hB
          exact hn ⟨hB, h'⟩
        · exact h'
  | .frame z (some sh) b, B, R, y, h => by
      simp only [cons, List.mem_append, List.mem_filter, decide_eq_true_eq] at h
      left
      simp only [uses, RSrc.dir, RSrc.crs, Option.getD_some, List.nil_append]
      rcases h with h | h
      · exact h
      · exact h.2
  | .form z b, B, R, y, h => by
      simp only [cons] at h
      simpa [uses, RSrc.dir, RSrc.crs] using cons_sub hσ b B R y h
  | .pat c p w b xs, B, R, y, h => by
      have h' : y ∈ cons σ B (patR R xs (intro σ B R c p xs)) p ∨
          y ∈ cons σ (patB B p xs) (patR R xs (intro σ B R c p xs)) b ∨ y ∈ cons σ B R w ∨
          y ∈ xs.getD [] := by
        simp only [cons] at h
        rcases List.mem_append.1 h with h1 | h1
        · rcases List.mem_append.1 h1 with h2 | h2
          · rcases List.mem_append.1 (List.mem_filter.1 h2).1 with h4 | h4
            · exact Or.inl h4
            · exact Or.inr (Or.inl h4)
          · exact Or.inr (Or.inr (Or.inl h2))
        · exact Or.inr (Or.inr (Or.inr h1))
      have key : y ∈ p.dir σ ∨ y ∈ w.dir σ ∨ y ∈ b.dir σ ∨ y ∈ xs.getD [] ∨ y ∈ p.crs ∨
          y ∈ w.crs ∨ y ∈ b.crs ∨ y ∈ B := by
        rcases h' with h | h | h | h
        · rcases cons_sub hσ p B _ y h with h' | h'
          · simp only [uses, List.mem_append] at h'
            tauto
          · tauto
        · rcases cons_sub hσ b _ _ y h with h' | h'
          · simp only [uses, List.mem_append] at h'
            tauto
          · simp only [patB, List.mem_append] at h'
            rcases h' with (h' | h') | h'
            · tauto
            · exact Or.inl (patNames_sub_dir σ p y h')
            · tauto
        · rcases cons_sub hσ w B R y h with h' | h'
          · simp only [uses, List.mem_append] at h'
            tauto
          · tauto
        · tauto
      simp only [uses, List.mem_append, mem_dir_pat, RSrc.crs]
      tauto
  | .quote c, B, R, y, h => by
      simp only [cons] at h
      simpa [uses, RSrc.dir, RSrc.crs] using cons_sub hσ c B R y h
  | .pquote c, B, R, y, h => by
      simp only [cons] at h
      simpa [uses, RSrc.dir, RSrc.crs] using cons_sub hσ c B R y h


/-! ## Contexts -/

/-- One frame of a context.  The hole sits at an expression, value, body,
frame-body or quotation position, never inside a pattern: a pattern decides
what its construct introduces, so a fragment plugged there is part of the
construct. -/
inductive RFrame (C : Type w) (S : Type u) (X : Type v) where
  | appL (a : RSrc C S X)
  | appR (f : RSrc C S X)
  | altL (t₂ : RSrc C S X)
  | altR (t₁ : RSrc C S X)
  | newB (ys : List X)
  | frameB (z : X) (xs : Option (List X))
  | formB (z : X)
  /-- the hole is the value of a pattern construct -/
  | patW (c : C) (p b : RSrc C S X) (xs : Option (List X))
  /-- the hole is the body of a pattern construct -/
  | patBd (c : C) (p w : RSrc C S X) (xs : Option (List X))
  | quoteB
  | pquoteB

namespace RFrame

/-- Put a fragment into the hole of a frame. -/
def plug : RFrame C S X → RSrc C S X → RSrc C S X
  | .appL a, t => .app t a
  | .appR f, t => .app f t
  | .altL t₂, t => .alt t t₂
  | .altR t₁, t => .alt t₁ t
  | .newB ys, t => .new ys t
  | .frameB z xs, t => .frame z xs t
  | .formB z, t => .form z t
  | .patW c p b xs, t => .pat c p t b xs
  | .patBd c p w xs, t => .pat c p w t xs
  | .quoteB, t => .quote t
  | .pquoteB, t => .pquote t

/-- A context, outermost frame first. -/
def plugAll : List (RFrame C S X) → RSrc C S X → RSrc C S X
  | [], t => t
  | F :: K, t => F.plug (plugAll K t)

/-- The binders in force at the hole of a frame (no implicit capture). -/
def bindIn (B : List X) : RFrame C S X → List X
  | .newB ys => B ++ ys
  | .frameB _ (some sh) => B ++ sh
  | .patBd _ p _ xs => patB B p xs
  | _ => B

/-- The binders in force at the hole of a context. -/
def holeB (B : List X) : List (RFrame C S X) → List X
  | [] => B
  | F :: K => holeB (F.bindIn B) K

/-- The child index of the hole. -/
def step : RFrame C S X → ℕ
  | .appL _ => 0
  | .appR _ => 1
  | .altL _ => 0
  | .altR _ => 1
  | .newB _ => 0
  | .frameB _ _ => 0
  | .formB _ => 0
  | .patW _ _ _ _ => 1
  | .patBd _ _ _ _ => 2
  | .quoteB => 0
  | .pquoteB => 0

/-- The position of the hole of a context. -/
def holePos (π : Owner) : List (RFrame C S X) → Owner
  | [] => π
  | F :: K => holePos (π ++ [F.step]) K

end RFrame

/-- Read the frames along the shape of `K` off a term of the same shape, and the
content of its hole. -/
def split {Y : Type v} : List (RFrame C S X) → RSrc C S Y → Option (List (RFrame C S Y) × RSrc C S Y)
  | [], T => some ([], T)
  | .appL _ :: K, .app f a => (split K f).map fun r => (.appL a :: r.1, r.2)
  | .appR _ :: K, .app f a => (split K a).map fun r => (.appR f :: r.1, r.2)
  | .altL _ :: K, .alt t₁ t₂ => (split K t₁).map fun r => (.altL t₂ :: r.1, r.2)
  | .altR _ :: K, .alt t₁ t₂ => (split K t₂).map fun r => (.altR t₁ :: r.1, r.2)
  | .newB _ :: K, .new ys b => (split K b).map fun r => (.newB ys :: r.1, r.2)
  | .frameB _ _ :: K, .frame z xs b => (split K b).map fun r => (.frameB z xs :: r.1, r.2)
  | .formB _ :: K, .form z b => (split K b).map fun r => (.formB z :: r.1, r.2)
  | .patW _ _ _ _ :: K, .pat c p w b xs => (split K w).map fun r => (.patW c p b xs :: r.1, r.2)
  | .patBd _ _ _ _ :: K, .pat c p w b xs => (split K b).map fun r => (.patBd c p w xs :: r.1, r.2)
  | .quoteB :: K, .quote c => (split K c).map fun r => (.quoteB :: r.1, r.2)
  | .pquoteB :: K, .pquote c => (split K c).map fun r => (.pquoteB :: r.1, r.2)
  | _ :: _, _ => none

/-- The crossing names in force at the hole of a frame. -/
def bindR (σ : Signature C) (B R : List X) : RFrame C S X → List X
  | .newB ys => without R ys
  | .frameB _ (some sh) => sh
  | .patBd c p _ xs => patR R xs (intro σ B R c p xs)
  | _ => R

/-- The crossing names in force at the hole of a context. -/
def holeR (σ : Signature C) : List X → List X → List (RFrame C S X) → List X
  | _, R, [] => R
  | B, R, F :: K => holeR σ (F.bindIn B) (bindR σ B R F) K

/-- **The names the resolution of a context reads from outside**, the hole
excluded.  Through a frame without a crossing set pass the names binders on its
path introduced (every name, under the lexical policy); through a sealed frame,
its shared names. -/
def consCtx (σ : Signature C) : List X → List X → List (RFrame C S X) → List X
  | _, _, [] => []
  | B, R, .appL a :: K => cons σ B R a ++ consCtx σ B R K
  | B, R, .appR f :: K => cons σ B R f ++ consCtx σ B R K
  | B, R, .altL t :: K => cons σ B R t ++ consCtx σ B R K
  | B, R, .altR t :: K => cons σ B R t ++ consCtx σ B R K
  | B, R, .newB ys :: K =>
      (consCtx σ (B ++ ys) (without R ys) K).filter fun y => decide (y ∉ ys)
  | B, R, .frameB _ none :: K =>
      (consCtx σ B R K).filter fun y => decide (y ∈ B ∨ σ.frame = .lexical)
  | B, _, .frameB _ (some sh) :: K =>
      sh ++ (consCtx σ (B ++ sh) sh K).filter fun y => decide (y ∈ sh)
  | B, R, .formB _ :: K => consCtx σ B R K
  | B, R, .patW c p b xs :: K =>
      (cons σ B (patR R xs (intro σ B R c p xs)) p ++
          cons σ (patB B p xs) (patR R xs (intro σ B R c p xs)) b).filter
          (fun y => decide (y ∉ intro σ B R c p xs)) ++
        consCtx σ B R K ++ xs.getD []
  | B, R, .patBd c p w xs :: K =>
      (cons σ B (patR R xs (intro σ B R c p xs)) p ++
          consCtx σ (patB B p xs) (patR R xs (intro σ B R c p xs)) K).filter
          (fun y => decide (y ∉ intro σ B R c p xs)) ++
        cons σ B R w ++ xs.getD []
  | B, R, .quoteB :: K => consCtx σ B R K
  | B, R, .pquoteB :: K => consCtx σ B R K

/-- A signature is **stable** when its frame policy is lexical or clause and it
has no implicit nested capture. -/
def Stable (σ : Signature C) : Prop :=
  (σ.frame = .lexical ∨ σ.frame = .clause) ∧ σ.capture = false

theorem bodyB_of_capture {σ : Signature C} (hc : σ.capture = false) (B : List X)
    (b : RSrc C S X) : bodyB σ B b = B := by
  simp [bodyB, hc]

/-- Under a stable signature a frame never owns a name passed in explicitly,
as long as those are among the binders on the path. -/
theorem filter_own_eq {σ : Signature C} (hs : Stable σ) {B R : List X}
    (hRB : ∀ y ∈ R, y ∈ B) (b : RSrc C S X) :
    without R (own σ B b) = R := by
  unfold without
  rw [List.filter_eq_self]
  intro y hy
  rcases hs.1 with hl | hcl
  · simp [own_lexical hl]
  · have : y ∉ own σ B b := fun h => ((mem_own_clause hcl).1 h).1 (hRB y hy)
    simp [this]

/-- The crossing names in force stay among the binders on the path. -/
theorem bindR_sub (σ : Signature C) {B R : List X} (hRB : ∀ y ∈ R, y ∈ B) :
    ∀ (F : RFrame C S X), ∀ y ∈ bindR σ B R F, y ∈ F.bindIn B
  | .appL _, y, h => hRB y h
  | .appR _, y, h => hRB y h
  | .altL _, y, h => hRB y h
  | .altR _, y, h => hRB y h
  | .newB ys, y, h => by
      simp only [bindR, without, List.mem_filter] at h
      simp [RFrame.bindIn, hRB y h.1]
  | .frameB _ none, y, h => hRB y h
  | .frameB _ (some sh), y, h => by
      simp only [bindR] at h
      simp [RFrame.bindIn, h]
  | .formB _, y, h => hRB y h
  | .patW _ _ _ _, y, h => hRB y h
  | .patBd c p w xs, y, h => by
      simp only [bindR, patR, without, List.mem_append, List.mem_filter] at h
      simp only [RFrame.bindIn, patB, List.mem_append]
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inl (hRB y h.1))
  | .quoteB, y, h => hRB y h
  | .pquoteB, y, h => hRB y h

/-- Every name a context reads from outside is read by every plugging of it. -/
theorem consCtx_sub_cons {σ : Signature C} (hs : Stable σ) :
    ∀ (K : List (RFrame C S X)) (B R : List X) (t : RSrc C S X), (∀ y ∈ R, y ∈ B) →
      ∀ y ∈ consCtx σ B R K, y ∈ cons σ B R (RFrame.plugAll K t)
  | [], _, _, _, _, y, h => by simp [consCtx] at h
  | .appL a :: K, B, R, t, hRB, y, h => by
      simp only [consCtx, List.mem_append] at h
      simp only [RFrame.plugAll, RFrame.plug, cons, List.mem_append]
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl (consCtx_sub_cons hs K B R t hRB y h)
  | .appR f :: K, B, R, t, hRB, y, h => by
      simp only [consCtx, List.mem_append] at h
      simp only [RFrame.plugAll, RFrame.plug, cons, List.mem_append]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (consCtx_sub_cons hs K B R t hRB y h)
  | .altL t₂ :: K, B, R, t, hRB, y, h => by
      simp only [consCtx, List.mem_append] at h
      simp only [RFrame.plugAll, RFrame.plug, cons, List.mem_append]
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl (consCtx_sub_cons hs K B R t hRB y h)
  | .altR t₁ :: K, B, R, t, hRB, y, h => by
      simp only [consCtx, List.mem_append] at h
      simp only [RFrame.plugAll, RFrame.plug, cons, List.mem_append]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (consCtx_sub_cons hs K B R t hRB y h)
  | .newB ys :: K, B, R, t, hRB, y, h => by
      simp only [consCtx, List.mem_filter, decide_eq_true_eq] at h
      simp only [RFrame.plugAll, RFrame.plug, cons, List.mem_filter, decide_eq_true_eq]
      exact ⟨consCtx_sub_cons hs K _ _ t (bindR_sub σ hRB (RFrame.newB ys : RFrame C S X)) y h.1, h.2⟩
  | .frameB z none :: K, B, R, t, hRB, y, h => by
      simp only [consCtx, List.mem_filter, decide_eq_true_eq] at h
      simp only [RFrame.plugAll, RFrame.plug, cons, List.mem_filter, decide_eq_true_eq,
        bodyB_of_capture hs.2, filter_own_eq hs hRB]
      refine ⟨consCtx_sub_cons hs K B R t hRB y h.1, ?_⟩
      rcases hs.1 with hl | hcl
      · rw [own_lexical hl]
        simp
      · rw [mem_own_clause hcl]
        rcases h.2 with hB | hl
        · exact fun h' => h'.1 hB
        · rw [hcl] at hl
          cases hl
  | .frameB z (some sh) :: K, B, R, t, hRB, y, h => by
      simp only [consCtx, List.mem_append, List.mem_filter, decide_eq_true_eq] at h
      simp only [RFrame.plugAll, RFrame.plug, cons, List.mem_append, List.mem_filter,
        decide_eq_true_eq]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨consCtx_sub_cons hs K _ _ t (bindR_sub σ hRB (RFrame.frameB z (some sh) : RFrame C S X)) y h.1,
          h.2⟩
  | .formB z :: K, B, R, t, hRB, y, h => by
      simp only [consCtx] at h
      simp only [RFrame.plugAll, RFrame.plug, cons]
      exact consCtx_sub_cons hs K B R t hRB y h
  | .patW c p b xs :: K, B, R, t, hRB, y, h => by
      simp only [consCtx, List.mem_append] at h
      simp only [RFrame.plugAll, RFrame.plug, cons, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (consCtx_sub_cons hs K B R t hRB y h))
      · exact Or.inr h
  | .patBd c p w xs :: K, B, R, t, hRB, y, h => by
      simp only [consCtx, List.mem_append] at h
      simp only [RFrame.plugAll, RFrame.plug, cons, List.mem_append]
      rcases h with (h | h) | h
      · left; left
        simp only [List.mem_filter, List.mem_append] at h ⊢
        rcases h with ⟨h1 | h1, h2⟩
        · exact ⟨Or.inl h1, h2⟩
        · exact ⟨Or.inr (consCtx_sub_cons hs K _ _ t (bindR_sub σ hRB (.patBd c p w xs)) y h1),
            h2⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .quoteB :: K, B, R, t, hRB, y, h => by
      simp only [consCtx] at h
      simp only [RFrame.plugAll, RFrame.plug, cons]
      exact consCtx_sub_cons hs K B R t hRB y h
  | .pquoteB :: K, B, R, t, hRB, y, h => by
      simp only [consCtx] at h
      simp only [RFrame.plugAll, RFrame.plug, cons]
      exact consCtx_sub_cons hs K B R t hRB y h

/-! ## L4: context stability -/

/-- **L4, context stability.**  For a stable signature (frame policy lexical or
clause, no implicit nested capture), and every context `K`: the frames read off
the resolution of `K[t]` are the same for every fragment `t` (and every
environment agreeing on the names the context reads from outside), and the
fragment is resolved at the binders, crossing names and position of the hole.
Plugging never moves an occurrence of the context to another binder. -/
theorem context_stable {σ : Signature C} (hs : Stable σ) :
    ∀ (K : List (RFrame C S X)) (E E' : REnv X) (B R : List X) (π : Owner)
      (t t' : RSrc C S X), (∀ y ∈ R, y ∈ B) →
      (∀ y ∈ consCtx σ B R K, E y = E' y) →
      ∃ (K' : List (RFrame C S (Owner × X))) (Eh Eh' : REnv X),
        split K (ann σ E B R π (RFrame.plugAll K t)) =
            some (K', ann σ Eh (RFrame.holeB B K) (holeR σ B R K) (RFrame.holePos π K) t) ∧
          split K (ann σ E' B R π (RFrame.plugAll K t')) =
            some (K', ann σ Eh' (RFrame.holeB B K) (holeR σ B R K) (RFrame.holePos π K) t')
  | [], E, E', B, R, π, t, t', _, _ => ⟨[], E, E', rfl, rfl⟩
  | .appL a :: K, E, E', B, R, π, t, t', hRB, h => by
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K E E' B R (π ++ [0]) t t' hRB
        (fun y hy => h y (by simp [consCtx, hy]))
      have ha : ann σ E B R (π ++ [1]) a = ann σ E' B R (π ++ [1]) a :=
        ann_congr σ a E E' B R _ (fun y hy => h y (by simp [consCtx, hy]))
      refine ⟨.appL (ann σ E B R (π ++ [1]) a) :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, ← ha, Option.map_some,
          RFrame.holeB, RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .appR f :: K, E, E', B, R, π, t, t', hRB, h => by
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K E E' B R (π ++ [1]) t t' hRB
        (fun y hy => h y (by simp [consCtx, hy]))
      have ha : ann σ E B R (π ++ [0]) f = ann σ E' B R (π ++ [0]) f :=
        ann_congr σ f E E' B R _ (fun y hy => h y (by simp [consCtx, hy]))
      refine ⟨.appR (ann σ E B R (π ++ [0]) f) :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, ← ha, Option.map_some,
          RFrame.holeB, RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .altL t₂ :: K, E, E', B, R, π, t, t', hRB, h => by
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K E E' B R (π ++ [0]) t t' hRB
        (fun y hy => h y (by simp [consCtx, hy]))
      have ha : ann σ E B R (π ++ [1]) t₂ = ann σ E' B R (π ++ [1]) t₂ :=
        ann_congr σ t₂ E E' B R _ (fun y hy => h y (by simp [consCtx, hy]))
      refine ⟨.altL (ann σ E B R (π ++ [1]) t₂) :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, ← ha, Option.map_some,
          RFrame.holeB, RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .altR t₁ :: K, E, E', B, R, π, t, t', hRB, h => by
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K E E' B R (π ++ [1]) t t' hRB
        (fun y hy => h y (by simp [consCtx, hy]))
      have ha : ann σ E B R (π ++ [0]) t₁ = ann σ E' B R (π ++ [0]) t₁ :=
        ann_congr σ t₁ E E' B R _ (fun y hy => h y (by simp [consCtx, hy]))
      refine ⟨.altR (ann σ E B R (π ++ [0]) t₁) :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, ← ha, Option.map_some,
          RFrame.holeB, RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .newB ys :: K, E, E', B, R, π, t, t', hRB, h => by
      have hag : ∀ y ∈ consCtx σ (B ++ ys) (without R ys) K,
          E.update ys π y = E'.update ys π y :=
        update_agree (fun y hy hn => h y (by simp [consCtx, hy, hn]))
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K _ _ (B ++ ys) (without R ys) (π ++ [0]) t t'
        (bindR_sub σ hRB (RFrame.newB ys : RFrame C S X)) hag
      refine ⟨.newB (ys.map fun y => (π, y)) :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .frameB z none :: K, E, E', B, R, π, t, t', hRB, h => by
      have hag : ∀ y ∈ consCtx σ B R K,
          E.update (own σ B (RFrame.plugAll K t)) π y =
            E'.update (own σ B (RFrame.plugAll K t')) π y := by
        intro y hy
        rcases hs.1 with hl | hcl
        · rw [own_lexical hl, own_lexical hl, update_not_mem List.not_mem_nil,
            update_not_mem List.not_mem_nil]
          exact h y (by simp [consCtx, hy, hl])
        · by_cases hB : y ∈ B
          · have hn : ∀ u : RSrc C S X, y ∉ own σ B u :=
              fun u hu => ((mem_own_clause hcl).1 hu).1 hB
            rw [update_not_mem (hn _), update_not_mem (hn _)]
            exact h y (by simp [consCtx, hy, hB])
          · have hm : ∀ u : RSrc C S X, y ∈ cons σ B R (RFrame.plugAll K u) →
                y ∈ own σ B (RFrame.plugAll K u) := by
              intro u hu
              rcases cons_sub hcl _ B R y hu with h' | h'
              · exact (mem_own_clause hcl).2 ⟨hB, h'⟩
              · exact absurd h' hB
            rw [update_mem (hm t (consCtx_sub_cons hs K B R t hRB y hy)),
              update_mem (hm t' (consCtx_sub_cons hs K B R t' hRB y hy))]
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K _ _ B R (π ++ [0]) t t' hRB hag
      refine ⟨.frameB (π, z) none :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, bodyB_of_capture hs.2, filter_own_eq hs hRB,
          split, h1, Option.map_some, RFrame.holeB, RFrame.bindIn, holeR, bindR, RFrame.holePos,
          RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, bodyB_of_capture hs.2, filter_own_eq hs hRB,
          split, h2, Option.map_some, RFrame.holeB, RFrame.bindIn, holeR, bindR, RFrame.holePos,
          RFrame.step]
  | .frameB z (some sh) :: K, E, E', B, R, π, t, t', hRB, h => by
      have hsh : ∀ y ∈ sh, E y = E' y := fun y hy => h y (by simp [consCtx, hy])
      have hRB' : ∀ y ∈ sh, y ∈ B ++ sh := fun y hy => by simp [hy]
      have hag : ∀ y ∈ consCtx σ (B ++ sh) sh K,
          E.update (sealOwn σ B sh (RFrame.plugAll K t)) π y =
            E'.update (sealOwn σ B sh (RFrame.plugAll K t')) π y := by
        intro y hy
        by_cases hs' : y ∈ sh
        · have hn : ∀ u : RSrc C S X, y ∉ sealOwn σ B sh u := by
            intro u hu
            simp [sealOwn, hs'] at hu
          rw [update_not_mem (hn _), update_not_mem (hn _)]
          exact hsh y hs'
        · have hm : ∀ u : RSrc C S X, y ∈ sealOwn σ B sh (RFrame.plugAll K u) := by
            intro u
            simp only [sealOwn, List.mem_dedup, List.mem_filter, decide_eq_true_eq]
            exact ⟨consCtx_sub_cons hs K _ _ u hRB' y hy, hs'⟩
          rw [update_mem (hm t), update_mem (hm t')]
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K _ _ (B ++ sh) sh (π ++ [0]) t t' hRB' hag
      have hmap : sh.map (fun y => (E y, y)) = sh.map (fun y => (E' y, y)) :=
        List.map_congr_left (fun y hy => by rw [hsh y hy])
      refine ⟨.frameB (π, z) (some (sh.map fun y => (E y, y))) :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, ← hmap, Option.map_some,
          RFrame.holeB, RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .formB z :: K, E, E', B, R, π, t, t', hRB, h => by
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K E E' B R (π ++ [0]) t t' hRB
        (fun y hy => h y (by simpa [consCtx] using hy))
      refine ⟨.formB (π, z) :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .patW c p b xs :: K, E, E', B, R, π, t, t', hRB, h => by
      have hp : ann σ (E.update (intro σ B R c p xs) π) B (patR R xs (intro σ B R c p xs))
            (π ++ [0]) p =
          ann σ (E'.update (intro σ B R c p xs) π) B (patR R xs (intro σ B R c p xs))
            (π ++ [0]) p :=
        ann_congr σ p _ _ _ _ _ (update_agree (fun y hy hn => h y (by simp [consCtx, hy, hn])))
      have hb : ann σ (E.update (intro σ B R c p xs) π) (patB B p xs)
            (patR R xs (intro σ B R c p xs)) (π ++ [2]) b =
          ann σ (E'.update (intro σ B R c p xs) π) (patB B p xs)
            (patR R xs (intro σ B R c p xs)) (π ++ [2]) b :=
        ann_congr σ b _ _ _ _ _ (update_agree (fun y hy hn => h y (by simp [consCtx, hy, hn])))
      have hx : xs.map (List.map fun y => (E y, y)) = xs.map (List.map fun y => (E' y, y)) := by
        cases xs with
        | none => rfl
        | some sh =>
            simp only [Option.map_some, Option.some.injEq]
            exact List.map_congr_left (fun y hy => by rw [h y (by simp [consCtx, hy])])
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K E E' B R (π ++ [1]) t t' hRB
        (fun y hy => h y (by simp [consCtx, hy]))
      refine ⟨.patW c
          (ann σ (E.update (intro σ B R c p xs) π) B (patR R xs (intro σ B R c p xs)) (π ++ [0]) p)
          (ann σ (E.update (intro σ B R c p xs) π) (patB B p xs) (patR R xs (intro σ B R c p xs))
            (π ++ [2]) b)
          (xs.map (List.map fun y => (E y, y))) :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, ← hp, ← hb, ← hx,
          Option.map_some, RFrame.holeB, RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .patBd c p w xs :: K, E, E', B, R, π, t, t', hRB, h => by
      have hag : ∀ y ∈ consCtx σ (patB B p xs) (patR R xs (intro σ B R c p xs)) K,
          E.update (intro σ B R c p xs) π y = E'.update (intro σ B R c p xs) π y :=
        update_agree (fun y hy hn => h y (by simp [consCtx, hy, hn]))
      have hp : ann σ (E.update (intro σ B R c p xs) π) B (patR R xs (intro σ B R c p xs))
            (π ++ [0]) p =
          ann σ (E'.update (intro σ B R c p xs) π) B (patR R xs (intro σ B R c p xs))
            (π ++ [0]) p :=
        ann_congr σ p _ _ _ _ _ (update_agree (fun y hy hn => h y (by simp [consCtx, hy, hn])))
      have hw : ann σ E B R (π ++ [1]) w = ann σ E' B R (π ++ [1]) w :=
        ann_congr σ w E E' B R _ (fun y hy => h y (by simp [consCtx, hy]))
      have hx : xs.map (List.map fun y => (E y, y)) = xs.map (List.map fun y => (E' y, y)) := by
        cases xs with
        | none => rfl
        | some sh =>
            simp only [Option.map_some, Option.some.injEq]
            exact List.map_congr_left (fun y hy => by rw [h y (by simp [consCtx, hy])])
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K _ _ (patB B p xs) (patR R xs (intro σ B R c p xs)) (π ++ [2]) t t'
        (bindR_sub σ hRB (.patBd c p w xs)) hag
      refine ⟨.patBd c
          (ann σ (E.update (intro σ B R c p xs) π) B (patR R xs (intro σ B R c p xs)) (π ++ [0]) p)
          (ann σ E B R (π ++ [1]) w) (xs.map (List.map fun y => (E y, y))) :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, ← hp, ← hw, ← hx,
          Option.map_some, RFrame.holeB, RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .quoteB :: K, E, E', B, R, π, t, t', hRB, h => by
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K E E' B R (π ++ [0]) t t' hRB
        (fun y hy => h y (by simpa [consCtx] using hy))
      refine ⟨.quoteB :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
  | .pquoteB :: K, E, E', B, R, π, t, t', hRB, h => by
      obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K E E' B R (π ++ [0]) t t' hRB
        (fun y hy => h y (by simpa [consCtx] using hy))
      refine ⟨.pquoteB :: K', Eh, Eh', ?_, ?_⟩
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h1, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]
      · simp only [RFrame.plugAll, RFrame.plug, ann, split, h2, Option.map_some, RFrame.holeB,
          RFrame.bindIn, holeR, bindR, RFrame.holePos, RFrame.step]

/-- **L4 in one environment.**  One annotated context serves every fragment. -/
theorem context_stable_one {σ : Signature C} (hs : Stable σ) (K : List (RFrame C S X))
    (E : REnv X) (B R : List X) (hRB : ∀ y ∈ R, y ∈ B) (π : Owner) (t t' : RSrc C S X) :
    ((split K (ann σ E B R π (RFrame.plugAll K t))).map Prod.fst) =
      ((split K (ann σ E B R π (RFrame.plugAll K t'))).map Prod.fst) := by
  obtain ⟨K', Eh, Eh', h1, h2⟩ := context_stable hs K E E B R π t t' hRB (fun _ _ => rfl)
  rw [h1, h2]
  rfl

/-! ## L3: independent calls -/

/-- All annotated store-name occurrences, crossing-set annotations included. -/
def occs {Y : Type v} : RSrc C S Y → List Y
  | .sv y => [y]
  | .app f a => occs f ++ occs a
  | .alt t₁ t₂ => occs t₁ ++ occs t₂
  | .new _ b => occs b
  | .frame _ xs b => xs.getD [] ++ occs b
  | .form _ b => occs b
  | .pat _ p w b xs => occs p ++ occs w ++ occs b ++ xs.getD []
  | .quote c => occs c
  | .pquote c => occs c
  | _ => []

theorem prefix_append_trans {π o : Owner} {i : List ℕ} (h : (π ++ i) <+: o) : π <+: o :=
  (List.prefix_append π i).trans h

/-- **Where an occurrence resolves**: to its environment, at a name the fragment
reads from outside, or to a binder at or below the fragment's position. -/
theorem ann_occ (σ : Signature C) :
    ∀ (t : RSrc C S X) (E : REnv X) (B R : List X) (π : Owner),
      ∀ q ∈ occs (ann σ E B R π t), (q.1 = E q.2 ∧ q.2 ∈ cons σ B R t) ∨ π <+: q.1
  | .sym _, _, _, _, _, q, h => by simp [ann, occs] at h
  | .fn _, _, _, _, _, q, h => by simp [ann, occs] at h
  | .sv y, E, B, R, π, q, h => by
      simp only [ann, occs, List.mem_singleton] at h
      subst h
      exact Or.inl ⟨rfl, by simp [cons]⟩
  | .par _, _, _, _, _, q, h => by simp [ann, occs] at h
  | .app f a, E, B, R, π, q, h => by
      simp only [ann, occs, List.mem_append] at h
      rcases h with h | h
      · rcases ann_occ σ f E B R _ q h with h' | h'
        · exact Or.inl ⟨h'.1, by simp [cons, h'.2]⟩
        · exact Or.inr (prefix_append_trans h')
      · rcases ann_occ σ a E B R _ q h with h' | h'
        · exact Or.inl ⟨h'.1, by simp [cons, h'.2]⟩
        · exact Or.inr (prefix_append_trans h')
  | .alt t₁ t₂, E, B, R, π, q, h => by
      simp only [ann, occs, List.mem_append] at h
      rcases h with h | h
      · rcases ann_occ σ t₁ E B R _ q h with h' | h'
        · exact Or.inl ⟨h'.1, by simp [cons, h'.2]⟩
        · exact Or.inr (prefix_append_trans h')
      · rcases ann_occ σ t₂ E B R _ q h with h' | h'
        · exact Or.inl ⟨h'.1, by simp [cons, h'.2]⟩
        · exact Or.inr (prefix_append_trans h')
  | .new ys b, E, B, R, π, q, h => by
      simp only [ann, occs] at h
      rcases ann_occ σ b _ _ _ _ q h with h' | h'
      · by_cases hm : q.2 ∈ ys
        · rw [update_mem hm] at h'
          exact Or.inr (h'.1 ▸ List.prefix_refl π)
        · rw [update_not_mem hm] at h'
          exact Or.inl ⟨h'.1, by simp [cons, h'.2, hm]⟩
      · exact Or.inr (prefix_append_trans h')
  | .frame z none b, E, B, R, π, q, h => by
      simp only [ann, occs, Option.getD_none, List.nil_append] at h
      rcases ann_occ σ b _ _ _ _ q h with h' | h'
      · by_cases hm : q.2 ∈ own σ B b
        · rw [update_mem hm] at h'
          exact Or.inr (h'.1 ▸ List.prefix_refl π)
        · rw [update_not_mem hm] at h'
          exact Or.inl ⟨h'.1, by simp [cons, h'.2, hm]⟩
      · exact Or.inr (prefix_append_trans h')
  | .frame z (some sh) b, E, B, R, π, q, h => by
      simp only [ann, occs, Option.getD_some, List.mem_append, List.mem_map] at h
      rcases h with ⟨y, hy, rfl⟩ | h
      · exact Or.inl ⟨rfl, by simp [cons, hy]⟩
      · rcases ann_occ σ b _ _ _ _ q h with h' | h'
        · by_cases hm : q.2 ∈ sealOwn σ B sh b
          · rw [update_mem hm] at h'
            exact Or.inr (h'.1 ▸ List.prefix_refl π)
          · rw [update_not_mem hm] at h'
            have hsh : q.2 ∈ sh := by
              by_contra hn
              exact hm (by simp [sealOwn, h'.2, hn])
            exact Or.inl ⟨h'.1, by simp [cons, hsh]⟩
        · exact Or.inr (prefix_append_trans h')
  | .form z b, E, B, R, π, q, h => by
      simp only [ann, occs] at h
      rcases ann_occ σ b E B R _ q h with h' | h'
      · exact Or.inl ⟨h'.1, by simp [cons, h'.2]⟩
      · exact Or.inr (prefix_append_trans h')
  | .pat c p w b xs, E, B, R, π, q, h => by
      simp only [ann, occs, List.mem_append] at h
      rcases h with ((h | h) | h) | h
      · rcases ann_occ σ p _ _ _ _ q h with h' | h'
        · by_cases hm : q.2 ∈ intro σ B R c p xs
          · rw [update_mem hm] at h'
            exact Or.inr (h'.1 ▸ List.prefix_refl π)
          · rw [update_not_mem hm] at h'
            exact Or.inl ⟨h'.1, by simp [cons, h'.2, hm]⟩
        · exact Or.inr (prefix_append_trans h')
      · rcases ann_occ σ w E B R _ q h with h' | h'
        · exact Or.inl ⟨h'.1, by simp [cons, h'.2]⟩
        · exact Or.inr (prefix_append_trans h')
      · rcases ann_occ σ b _ _ _ _ q h with h' | h'
        · by_cases hm : q.2 ∈ intro σ B R c p xs
          · rw [update_mem hm] at h'
            exact Or.inr (h'.1 ▸ List.prefix_refl π)
          · rw [update_not_mem hm] at h'
            exact Or.inl ⟨h'.1, by simp [cons, h'.2, hm]⟩
        · exact Or.inr (prefix_append_trans h')
      · cases xs with
        | none => simp at h
        | some sh =>
            simp only [Option.map_some, Option.getD_some, List.mem_map] at h
            obtain ⟨y, hy, rfl⟩ := h
            exact Or.inl ⟨rfl, by simp [cons, hy]⟩
  | .quote c, E, B, R, π, q, h => by
      simp only [ann, occs] at h
      rcases ann_occ σ c E B R _ q h with h' | h'
      · exact Or.inl ⟨h'.1, by simp [cons, h'.2]⟩
      · exact Or.inr (prefix_append_trans h')
  | .pquote c, E, B, R, π, q, h => by
      simp only [ann, occs] at h
      rcases ann_occ σ c E B R _ q h with h' | h'
      · exact Or.inl ⟨h'.1, by simp [cons, h'.2]⟩
      · exact Or.inr (prefix_append_trans h')

/-- **L3, independent calls.**  Under the clause policy, every occurrence inside
a frame whose spelling no binder on the frame's path introduced resolves to the
frame or to a binder inside it.  Each run of the frame renames those, so runs
share only the names binders on the path introduced. -/
theorem private_inside {σ : Signature C} (hσ : σ.frame = .clause) (E : REnv X) (B R : List X)
    (π : Owner) (z : X) (b : RSrc C S X) :
    ∀ q ∈ occs (ann σ E B R π (.frame z none b)), q.2 ∉ B → π <+: q.1 := by
  intro q hq hB
  simp only [ann, occs, Option.getD_none, List.nil_append] at hq
  rcases ann_occ σ b _ _ _ _ q hq with h' | h'
  · have hown : q.2 ∈ own σ B b := by
      rw [mem_own_clause hσ]
      refine ⟨hB, ?_⟩
      unfold bodyB at h'
      split at h'
      · rcases cons_sub hσ b _ _ q.2 h'.2 with h'' | h''
        · exact h''
        · simp only [List.mem_append] at h''
          rcases h'' with h'' | h''
          · exact absurd h'' hB
          · exact ((mem_own_clause hσ).1 h'').2
      · rcases cons_sub hσ b _ _ q.2 h'.2 with h'' | h''
        · exact h''
        · exact absurd h'' hB
    rw [h'.1, update_mem hown]
    exact List.prefix_refl π
  · exact prefix_append_trans h'

/-- **L3 for sealed frames**, under every frame policy: an occurrence inside a
frame with a crossing set resolves inside it unless its spelling is shared. -/
theorem private_inside_sealed (σ : Signature C) (E : REnv X) (B R : List X) (π : Owner) (z : X)
    (sh : List X) (b : RSrc C S X) :
    ∀ q ∈ occs (ann σ E B R π (.frame z (some sh) b)), q.2 ∉ sh → π <+: q.1 := by
  intro q hq hsh
  simp only [ann, occs, Option.getD_some, List.mem_append, List.mem_map] at hq
  rcases hq with ⟨y, hy, rfl⟩ | hq
  · exact absurd hy hsh
  · rcases ann_occ σ b _ _ _ _ q hq with h' | h'
    · have hm : q.2 ∈ sealOwn σ B sh b := by simp [sealOwn, h'.2, hsh]
      rw [h'.1, update_mem hm]
      exact List.prefix_refl π
    · exact prefix_append_trans h'

/-! ## L6: one unknown per name per frame -/

/-- The occurrences in expression, relation, value and quotation positions,
reached without crossing a binder: not below an arrow, a `new` block, a frame
or a construct with a crossing set. -/
def relOccs (σ : Signature C) {Y : Type v} : RSrc C S Y → List Y
  | .sv y => [y]
  | .app f a => relOccs σ f ++ relOccs σ a
  | .alt t₁ t₂ => relOccs σ t₁ ++ relOccs σ t₂
  | .form _ b => relOccs σ b
  | .pat c p w b none =>
      (if σ.role c = .rel then relOccs σ p ++ relOccs σ b else []) ++ relOccs σ w
  | .pat _ _ w _ (some _) => relOccs σ w
  | .quote c => relOccs σ c
  | .pquote c => relOccs σ c
  | _ => []

theorem update_nil (E : REnv X) (o : Owner) : E.update [] o = E := by
  funext y
  simp [REnv.update]

/-- **L6, pan-unification.**  Every occurrence reached through relations,
expressions and values only denotes the unknown its environment gives the
spelling: one name, one unknown.  A relation introduces nothing, so sibling
relations that write one name denote one unknown. -/
theorem relOccs_env (σ : Signature C) :
    ∀ (t : RSrc C S X) (E : REnv X) (B R : List X) (π : Owner),
      ∀ q ∈ relOccs σ (ann σ E B R π t), q.1 = E q.2
  | .sym _, _, _, _, _, q, h => by simp [ann, relOccs] at h
  | .fn _, _, _, _, _, q, h => by simp [ann, relOccs] at h
  | .sv y, E, B, R, π, q, h => by
      simp only [ann, relOccs, List.mem_singleton] at h
      subst h
      rfl
  | .par _, _, _, _, _, q, h => by simp [ann, relOccs] at h
  | .app f a, E, B, R, π, q, h => by
      simp only [ann, relOccs, List.mem_append] at h
      rcases h with h | h
      · exact relOccs_env σ f E B R _ q h
      · exact relOccs_env σ a E B R _ q h
  | .alt t₁ t₂, E, B, R, π, q, h => by
      simp only [ann, relOccs, List.mem_append] at h
      rcases h with h | h
      · exact relOccs_env σ t₁ E B R _ q h
      · exact relOccs_env σ t₂ E B R _ q h
  | .new _ _, _, _, _, _, q, h => by simp [ann, relOccs] at h
  | .frame _ none _, _, _, _, _, q, h => by simp [ann, relOccs] at h
  | .frame _ (some _) _, _, _, _, _, q, h => by simp [ann, relOccs] at h
  | .form z b, E, B, R, π, q, h => by
      simp only [ann, relOccs] at h
      exact relOccs_env σ b E B R _ q h
  | .pat c p w b none, E, B, R, π, q, h => by
      simp only [ann, relOccs, Option.map_none, List.mem_append] at h
      rcases h with h | h
      · by_cases hr : σ.role c = .rel
        · have hi : intro σ B R c p none = [] := by simp [intro, hr]
          rw [if_pos hr, hi, update_nil] at h
          simp only [List.mem_append] at h
          rcases h with h | h
          · exact relOccs_env σ p E B _ _ q h
          · exact relOccs_env σ b E _ _ _ q h
        · rw [if_neg hr] at h
          simp at h
      · exact relOccs_env σ w E B R _ q h
  | .pat c p w b (some sh), E, B, R, π, q, h => by
      simp only [ann, relOccs, Option.map_some] at h
      exact relOccs_env σ w E B R _ q h
  | .quote c, E, B, R, π, q, h => by
      simp only [ann, relOccs] at h
      exact relOccs_env σ c E B R _ q h
  | .pquote c, E, B, R, π, q, h => by
      simp only [ann, relOccs] at h
      exact relOccs_env σ c E B R _ q h

/-- **Relations in a clause frame denote the frame's unknowns.**  Inside a
frame at `π` under the clause policy, every relation or expression occurrence
of the body's own level whose spelling no binder on the path introduced
denotes the frame's unknown of that spelling. -/
theorem relation_occ_frame {σ : Signature C} (hσ : σ.frame = .clause) (E : REnv X)
    (B : List X) (π : Owner) (b : RSrc C S X) (y : X) (hy : y ∈ uses σ b) (hB : y ∉ B) :
    (E.update (own σ B b) π) y = π :=
  update_mem ((mem_own_clause hσ).2 ⟨hB, hy⟩)

end Mettapedia.GSLT.LanguageDef.TemplateScope.Roles
