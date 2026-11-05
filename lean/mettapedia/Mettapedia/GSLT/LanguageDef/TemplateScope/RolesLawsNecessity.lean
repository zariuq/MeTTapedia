import Mettapedia.GSLT.LanguageDef.TemplateScope.RolesLaws

/-!
# Binding by role: each condition of the laws is needed

`TemplateScope.RolesLaws` proves L3 for the clause policy and L4 for stable
signatures.  Here each condition is shown necessary, for every signature, with
one spelling as the only assumption about names.

* `not_L3_of_not_clause` — a frame that does not own every name written at its
  level (lexical, or owning only what its relations write) lets a name written
  only inside it resolve outside it: two runs share it.
* `not_L4_relNames` — owning only the names relations write moves a binder of
  the context: plugging a relation that writes `$y` next to an expression `$y`
  moves that `$y` from the scope around into the frame (C's
  `queryNames_moves_binder`, for every signature with a relation).
* `not_L4_capture` — implicit nested capture moves a binder of the context:
  plugging `$y` next to a nested frame that writes `$y` moves the nested
  frame's `$y` to the enclosing frame (Gödel's decision B).
* `laws_iff` — **L3 and L4 hold together exactly when the frame policy is
  clause and there is no implicit nested capture**, whatever the roles of the
  pattern constructs.
* `sibling_relations_join`, `sibling_arrows_apart` — the role decides L6:
  sibling relations writing one name denote one unknown; sibling arrows denote
  two.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Roles

open Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v w

variable {C : Type w} {S : Type u} {X : Type v} [DecidableEq X]

/-- L4, as a property of a signature: one annotated context for every
fragment. -/
def L4Holds (σ : Signature C) (S : Type u) : Prop :=
  ∀ (K : List (RFrame C S X)) (E : REnv X) (B R : List X) (π : Owner) (t t' : RSrc C S X),
    (∀ y ∈ R, y ∈ B) →
    (split K (ann σ E B R π (RFrame.plugAll K t))).map Prod.fst =
      (split K (ann σ E B R π (RFrame.plugAll K t'))).map Prod.fst

/-- L3, as a property of a signature: inside a frame, a name no binder on its
path introduced resolves to the frame or below. -/
def L3Holds (σ : Signature C) (S : Type u) : Prop :=
  ∀ (E : REnv X) (B R : List X) (π : Owner) (z : X) (b : RSrc C S X),
    ∀ q ∈ occs (ann σ E B R π (.frame z none b)), q.2 ∉ B → π <+: q.1

theorem L4Holds_of_stable {σ : Signature C} (hs : Stable σ) : L4Holds (X := X) σ S :=
  fun K E B R π t t' hRB => context_stable_one hs K E B R hRB π t t'

theorem L3Holds_of_clause {σ : Signature C} (hσ : σ.frame = .clause) : L3Holds (X := X) σ S :=
  fun E B R π z b => private_inside hσ E B R π z b

/-- The environment that puts every name outside, at `[9]`. -/
def outside : REnv X := fun _ => [9]

/-- **L3 needs the clause policy.**  Under the lexical policy, or when a frame
owns only what its relations write, `(lam y $y)` resolves its `$y` outside the
frame. -/
theorem not_L3_of_not_clause {σ : Signature C} (hσ : σ.frame ≠ .clause) (y : X) :
    ¬ L3Holds (X := X) σ S := by
  intro h
  have hown : own σ [] (RSrc.sv y : RSrc C S X) = [] := by
    unfold own
    cases hf : σ.frame with
    | lexical => rfl
    | relNames => rfl
    | clause => exact absurd hf hσ
  have hmem : (([9], y) : Owner × X) ∈
      occs (ann σ outside [] [] [1] (.frame y none (RSrc.sv y : RSrc C S X))) := by
    simp only [ann, hown, update_nil, occs, Option.getD_none, List.nil_append, outside,
      List.mem_singleton]
  have := h outside [] [] [1] y (.sv y) _ hmem List.not_mem_nil
  simp at this

/-- **L4 fails when a frame owns only what its relations write**: in
`(lam y (□ $y))`, the hole `$y`-free parameter leaves the context's `$y` to the
scope around; a relation writing `$y` makes the frame own it. -/
theorem not_L4_relNames {σ : Signature C} (hσ : σ.frame = .relNames) (c : C)
    (hcr : σ.role c = .rel) (y : X) : ¬ L4Holds (X := X) σ S := by
  intro h
  have := h [.frameB y none, .appL (.sv y)] outside [] [] [] (.par y)
    (.pat c (.sv y) (.par y) (.par y) none) (fun _ h => h)
  simp [RFrame.plugAll, RFrame.plug, ann, split, own, hσ, RSrc.relUses, hcr, RSrc.patNames,
    REnv.update, outside] at this

/-- **L4 fails with implicit nested capture**: in `(lam y (□ (lam y $y)))` the
nested lambda owns its `$y` while nothing else writes `$y`; plugging `$y` into
the hole makes the enclosing lambda own `$y`, which the nested lambda then
captures. -/
theorem not_L4_capture {σ : Signature C} (hσ : σ.frame = .clause) (hc : σ.capture = true)
    (y : X) : ¬ L4Holds (X := X) σ S := by
  intro h
  have := h [.frameB y none, .appL (.frame y none (.sv y))] outside [] [] [] (.par y) (.sv y)
    (fun _ h => h)
  simp [RFrame.plugAll, RFrame.plug, ann, split, own, hσ, bodyB, hc, RSrc.dir, RSrc.crs,
    REnv.update] at this

/-- **L3 and L4 together single out the principle's frame rule**: a frame owns
every name written at its level that no binder on its path introduced, and its
owned names are not binders for what it contains.  The roles of the pattern
constructs are not constrained by either law. -/
theorem laws_iff (σ : Signature C) (y : X) :
    (L3Holds (X := X) σ S ∧ L4Holds (X := X) σ S) ↔ (σ.frame = .clause ∧ σ.capture = false) := by
  constructor
  · rintro ⟨h3, h4⟩
    by_cases hσ : σ.frame = .clause
    · refine ⟨hσ, ?_⟩
      cases hc : σ.capture with
      | false => rfl
      | true => exact absurd h4 (not_L4_capture hσ hc y)
    · exact absurd h3 (not_L3_of_not_clause hσ y)
  · rintro ⟨hσ, hc⟩
    exact ⟨L3Holds_of_clause hσ, L4Holds_of_stable ⟨Or.inr hσ, hc⟩⟩

/-! ## L6: the role decides who joins -/

/-- **Sibling relations join.**  Two sibling relations writing `$x` resolve both
pattern occurrences to the one unknown the environment gives `$x`. -/
theorem sibling_relations_join (σ : Signature C) (c : C) (hcr : σ.role c = .rel) (x : X)
    (E : REnv X) (B R : List X) (π : Owner) (w : RSrc C S X) :
    ann σ E B R π (.app (.pat c (.sv x) w w none) (.pat c (.sv x) w w none)) =
      .app (.pat c (.sv (E x, x)) (ann σ E B R (π ++ [0] ++ [1]) w)
          (ann σ E (patB B (RSrc.sv x : RSrc C S X) none) (patR R none []) (π ++ [0] ++ [2]) w)
          none)
        (.pat c (.sv (E x, x)) (ann σ E B R (π ++ [1] ++ [1]) w)
          (ann σ E (patB B (RSrc.sv x : RSrc C S X) none) (patR R none []) (π ++ [1] ++ [2]) w)
          none) := by
  have hi : intro σ B R c (.sv x : RSrc C S X) none = [] := by simp [intro, hcr]
  simp only [ann, hi, update_nil, Option.map_none]

/-- **Sibling arrows stay apart.**  Two sibling shadowing arrows writing a name
`$x` that is not passed in resolve their pattern occurrences to their own
positions. -/
theorem sibling_arrows_apart (σ : Signature C) (c : C) (hca : σ.role c = .arrow .shadow) (x : X)
    (E : REnv X) (B R : List X) (hx : x ∉ R) (π : Owner) (w : RSrc C S X) :
    ann σ E B R π (.app (.pat c (.sv x) w w none) (.pat c (.sv x) w w none)) =
      .app (.pat c (.sv (π ++ [0], x)) (ann σ E B R (π ++ [0] ++ [1]) w)
          (ann σ (E.update [x] (π ++ [0])) (patB B (RSrc.sv x : RSrc C S X) none)
            (patR R none [x]) (π ++ [0] ++ [2]) w)
          none)
        (.pat c (.sv (π ++ [1], x)) (ann σ E B R (π ++ [1] ++ [1]) w)
          (ann σ (E.update [x] (π ++ [1])) (patB B (RSrc.sv x : RSrc C S X) none)
            (patR R none [x]) (π ++ [1] ++ [2]) w)
          none) := by
  have hi : intro σ B R c (.sv x : RSrc C S X) none = [x] := by
    simp [intro, hca, RSrc.patNames, hx]
  simp only [ann, hi, Option.map_none]
  simp [REnv.update]

end Mettapedia.GSLT.LanguageDef.TemplateScope.Roles
