import Mettapedia.Logic.LinearLogic.KnowledgeTensorFrames

/-!
# Witnessed runs over frames: the fibred structure

In the frame-indexed calculus (`IndexedSystem`), knowledge and atoms live over a category of frames,
and each firing moves along its declaration's frame map, carrying atoms and transporting knowledge.
A run lies over a frame map: the composite of the frame maps of its firings.

* `Path`: **a witnessed run over a frame map**. Each firing records its declaration, its frame of
  untouched atoms, its admission, and the state and frame map it leaves; every index is tied to the
  data by an equation, so the operations below need no transport.
* `Path.run`, `Path.exists_iff_run`: witnessed runs exist exactly where runs exist, with the same
  word over the same frame map. `Path.route_eq`, `Path.eq_of_uses`: the frame map and the witnessed
  run are determined by the word.
* The operations: `identity`, `leaf`, `cut` over the composite frame map, `frame` and `strengthen`.
* **The fibred laws** (`Path.frame_cut`, `Path.strengthen_cut`): framing a cut frames its second
  part by the atoms carried along the first part's frame map, and strengthening a cut strengthens
  its second part by the knowledge transported along it. Framing and strengthening keep the frame
  map: they act in the fibres. With `cut_assoc`, `done_cut`, `cut_done`, `frame_zero`,
  `frame_frame`, `frame_done`, `strengthen_leaf`, `strengthen_done`, `strengthen_frame`, these are
  the structural equations of the frame-indexed calculus, each up to the equations of its indices.
* `FibredModel`: a proof-relevant model over frames: morphisms over frame maps, the five operations,
  and exactly these laws. `paths`: the witnessed runs are one.
* `lift`, `lift_unique`, `paths_initial`: **the witnessed runs over frames are the initial
  proof-relevant model of the frame-indexed calculus.**
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Fibred

open Mettapedia.Logic.LinearLogic.KnowledgeTensor
open _root_.CategoryTheory

universe uF uH uK uAtom uRule uM uN

variable {Frame : Type uF} [Category.{uH} Frame] {K : Frame → Type uK} [∀ a, SemilatticeInf (K a)]
  {Atom : Frame → Type uAtom} {Rule : Frame → Type uRule}

/-- Transport of a family over frames along equations of its indices, the frames fixed. -/
def recast {H : (a : Frame) → K a → Multiset (Atom a) → (b : Frame) → (a ⟶ b) → K b →
      Multiset (Atom b) → Type uM}
    {a b : Frame} {k j : K a} {Γ Δ : Multiset (Atom a)} {f g : a ⟶ b} {k' j' : K b}
    {Γ' Δ' : Multiset (Atom b)} (hk : k = j) (hΓ : Γ = Δ) (hf : f = g) (hk' : k' = j') (hΓ' : Γ' = Δ')
    (x : H a k Γ b f k' Γ') : H a j Δ b g j' Δ' := by
  subst hk hΓ hf hk' hΓ'
  exact x

/-- **A witnessed run over a frame map.** -/
inductive Path (sys : IndexedSystem Frame K Atom Rule) :
    (a : Frame) → K a → Multiset (Atom a) → (b : Frame) → (a ⟶ b) → K b → Multiset (Atom b) →
      Type (max uF uH uK uAtom uRule)
  | done {a : Frame} {k k' : K a} {Γ Γ' : Multiset (Atom a)} {f : a ⟶ a} (route : f = 𝟙 a)
      (told : k' = k) (target : Γ' = Γ) : Path sys a k Γ a f k' Γ'
  | fire {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
      {Γ' : Multiset (Atom b)} (declaration : Rule a) (frame : Multiset (Atom a))
      {k₁ : K (sys.target declaration)} {Γ₁ : Multiset (Atom (sys.target declaration))}
      {along : sys.target declaration ⟶ b} {k'' : K b} {Γ'' : Multiset (Atom b)}
      (source : Γ = sys.premises declaration + frame)
      (asked : sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration))
      (told : k₁ = sys.know (sys.extend declaration) k ⊓ sys.tell declaration)
      (target : Γ₁ = sys.conclusions declaration + sys.carried (sys.extend declaration) frame)
      (route : f = sys.extend declaration ≫ along) (finalKnowledge : k' = k'')
      (finalAtoms : Γ' = Γ'') (rest : Path sys (sys.target declaration) k₁ Γ₁ b along k'' Γ'') :
      Path sys a k Γ b f k' Γ'

namespace Path

variable {sys : IndexedSystem Frame K Atom Rule}

/-- The word of a witnessed run. -/
def uses : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)}, Path sys a k Γ b f k' Γ' → List (Sigma Rule)
  | _, _, _, _, _, _, _, .done _ _ _ => []
  | a, _, _, _, _, _, _, .fire declaration _ _ _ _ _ _ _ _ rest => ⟨a, declaration⟩ :: uses rest

/-- **A witnessed run is a run of its word over its frame map.** -/
theorem run {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (p : Path sys a k Γ b f k' Γ') : sys.Run a k Γ p.uses b f k' Γ' := by
  induction p with
  | done route told target =>
      subst route told target
      exact IndexedSystem.Run.done _ _ _
  | fire _ frame source asked told target route finalKnowledge finalAtoms _ ih =>
      subst route finalKnowledge finalAtoms
      exact IndexedSystem.Run.fire ⟨frame, source, asked, told, target⟩ ih

/-- A run has a witnessed run with its word. -/
theorem exists_of_run {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
    {b : Frame} {f : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)} (run : sys.Run a k Γ uses b f k' Γ') :
    ∃ p : Path sys a k Γ b f k' Γ', p.uses = uses := by
  induction run with
  | done a k Γ => exact ⟨.done rfl rfl rfl, rfl⟩
  | fire fires _ ih =>
      obtain ⟨frame, source, asked, told, target⟩ := fires
      obtain ⟨p, same⟩ := ih
      exact ⟨.fire _ frame source asked told target rfl rfl rfl p, by rw [← same]; rfl⟩

/-- **Witnessed runs exist exactly where runs exist**, with the same word over the same frame map. -/
theorem exists_iff_run {a : Frame} (k : K a) (Γ : Multiset (Atom a)) (uses : List (Sigma Rule))
    {b : Frame} (f : a ⟶ b) (k' : K b) (Γ' : Multiset (Atom b)) :
    (∃ p : Path sys a k Γ b f k' Γ', p.uses = uses) ↔ sys.Run a k Γ uses b f k' Γ' :=
  ⟨fun ⟨p, same⟩ => same ▸ p.run, exists_of_run⟩

/-- **The frame map of a witnessed run is determined by its word.** -/
theorem route_eq : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b}
    {k' : K b} {Γ' : Multiset (Atom b)} (p : Path sys a k Γ b f k' Γ') {j : K a}
    {Δ : Multiset (Atom a)} {g : a ⟶ b} {j' : K b} {Δ' : Multiset (Atom b)}
    (q : Path sys a j Δ b g j' Δ'), p.uses = q.uses → f = g
  | _, _, _, _, _, _, _, .done route _ _, _, _, _, _, _, .done route' _ _, _ => route.trans route'.symm
  | _, _, _, _, _, _, _, .done _ _ _, _, _, _, _, _, .fire _ _ _ _ _ _ _ _ _ _, same =>
      absurd same (List.cons_ne_nil _ _).symm
  | _, _, _, _, _, _, _, .fire _ _ _ _ _ _ _ _ _ _, _, _, _, _, _, .done _ _ _, same =>
      absurd same (List.cons_ne_nil _ _)
  | _, _, _, _, _, _, _, .fire declaration _ _ _ _ _ route _ _ rest, _, _, _, _, _,
      .fire declaration' _ _ _ _ _ route' _ _ rest', same => by
      have words : (⟨_, declaration⟩ :: rest.uses : List (Sigma Rule)) =
          ⟨_, declaration'⟩ :: rest'.uses := same
      obtain ⟨head, later⟩ := List.cons.inj words
      obtain rfl : declaration = declaration' := eq_of_heq (Sigma.mk.inj head).2
      rw [route, route', route_eq rest rest' later]

/-- **A witnessed run is determined by its word**, its source and its target. -/
theorem eq_of_uses {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (p q : Path sys a k Γ b f k' Γ') : p.uses = q.uses → p = q := by
  induction p with
  | done route told target =>
      intro same
      cases q with
      | done => rfl
      | fire => exact absurd same (List.cons_ne_nil _ _).symm
  | fire declaration frame source asked told target route finalKnowledge finalAtoms rest ih =>
      intro same
      cases q with
      | done => exact absurd same (List.cons_ne_nil _ _)
      | fire declaration' frame' source' asked' told' target' route' finalKnowledge' finalAtoms' rest' =>
          have words : (⟨_, declaration⟩ :: rest.uses : List (Sigma Rule)) =
              ⟨_, declaration'⟩ :: rest'.uses := same
          obtain ⟨head, later⟩ := List.cons.inj words
          obtain rfl : declaration = declaration' := eq_of_heq (Sigma.mk.inj head).2
          obtain rfl : frame = frame' := add_left_cancel (source.symm.trans source')
          have alongSame := route_eq rest rest' later
          subst alongSame told told' target target' finalKnowledge finalKnowledge' finalAtoms finalAtoms'
          rw [ih rest' later]

/-! ### The operations -/

/-- The witnessed run that does nothing. -/
def identity (a : Frame) (k : K a) (Γ : Multiset (Atom a)) : Path sys a k Γ a (𝟙 a) k Γ :=
  .done rfl rfl rfl

/-- The witnessed run of one use over nothing else. -/
def leaf {a : Frame} (declaration : Rule a) (k : K a)
    (asked : sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)) :
    Path sys a k (sys.premises declaration) (sys.target declaration) (sys.extend declaration)
      (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) (sys.conclusions declaration) :=
  .fire declaration 0 (add_zero _).symm asked rfl
    (by rw [IndexedSystem.carried_zero, add_zero]) (Category.comp_id _).symm rfl rfl (.done rfl rfl rfl)

/-- **Cut**: one witnessed run after another, over the composite frame map. -/
def cut : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k₁ : K b}
    {Γ₁ : Multiset (Atom b)} {c : Frame} {g : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)},
    Path sys a k Γ b f k₁ Γ₁ → Path sys b k₁ Γ₁ c g k' Γ' → Path sys a k Γ c (f ≫ g) k' Γ'
  | _, _, _, _, _, _, _, _, _, _, _, .done route told target, q =>
      recast (H := Path sys) told target (by rw [route, Category.id_comp]) rfl rfl q
  | _, _, _, _, _, _, _, _, _, _, _, .fire declaration frame source asked told target route
      finalKnowledge finalAtoms rest, q =>
      .fire declaration frame source asked told target (by rw [route, Category.assoc]) rfl rfl
        (cut rest (recast (H := Path sys) finalKnowledge finalAtoms rfl rfl rfl q))

/-- **Framing**: extra atoms beside the source, carried along the frame map to the target. -/
def frame : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (extra : Multiset (Atom a)),
    Path sys a k Γ b f k' Γ' → Path sys a k (Γ + extra) b f k' (Γ' + sys.carried f extra)
  | _, _, _, _, _, _, _, extra, .done route told target =>
      .done route told (by rw [target, route, IndexedSystem.carried_id])
  | _, _, _, _, _, _, _, extra, .fire declaration φ source asked told target route finalKnowledge
      finalAtoms rest =>
      .fire declaration (φ + extra) (by rw [source, add_assoc]) asked told
        (by rw [target, IndexedSystem.carried_add, add_assoc]) route finalKnowledge
        (by rw [finalAtoms, route, IndexedSystem.carried_comp])
        (frame (sys.carried (sys.extend declaration) extra) rest)

/-- **Strengthening**: extra knowledge at the source, transported along the frame map. -/
def strengthen : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (more : K a),
    Path sys a k Γ b f k' Γ' → Path sys a (k ⊓ more) Γ b f (k' ⊓ sys.know f more) Γ'
  | _, _, _, _, _, _, _, more, .done route told target =>
      .done route (by rw [told, route, sys.know_id]) target
  | _, _, _, _, _, _, _, more, .fire declaration φ source asked told target route finalKnowledge
      finalAtoms rest =>
      .fire declaration φ source
        (by
          rw [sys.know_inf]
          exact sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked)
        (by rw [told, sys.know_inf, inf_right_comm]) target route
        (by rw [finalKnowledge, route, sys.know_comp]) finalAtoms
        (strengthen (sys.know (sys.extend declaration) more) rest)

/-! ### Words of the operations -/

theorem uses_recast {a b : Frame} {k j : K a} {Γ Δ : Multiset (Atom a)} {f g : a ⟶ b} {k' j' : K b}
    {Γ' Δ' : Multiset (Atom b)} (hk : k = j) (hΓ : Γ = Δ) (hf : f = g) (hk' : k' = j')
    (hΓ' : Γ' = Δ') (p : Path sys a k Γ b f k' Γ') :
    (recast (H := Path sys) hk hΓ hf hk' hΓ' p).uses = p.uses := by
  subst hk hΓ hf hk' hΓ'
  rfl

theorem uses_cut : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b}
    {k₁ : K b} {Γ₁ : Multiset (Atom b)} {c : Frame} {g : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)}
    (p : Path sys a k Γ b f k₁ Γ₁) (q : Path sys b k₁ Γ₁ c g k' Γ'), (cut p q).uses = p.uses ++ q.uses
  | _, _, _, _, _, _, _, _, _, _, _, .done _ _ _, q => uses_recast _ _ _ _ _ q
  | _, _, _, _, _, _, _, _, _, _, _, .fire _ _ _ _ _ _ _ _ _ rest, q => by
      show _ :: (cut rest _).uses = _ :: (rest.uses ++ q.uses)
      rw [uses_cut rest, uses_recast]

theorem uses_frame : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b}
    {k' : K b} {Γ' : Multiset (Atom b)} (extra : Multiset (Atom a)) (p : Path sys a k Γ b f k' Γ'),
    (frame extra p).uses = p.uses
  | _, _, _, _, _, _, _, _, .done _ _ _ => rfl
  | _, _, _, _, _, _, _, _, .fire _ _ _ _ _ _ _ _ _ rest => by
      show _ :: (frame _ rest).uses = _ :: rest.uses
      rw [uses_frame]

theorem uses_strengthen : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b}
    {k' : K b} {Γ' : Multiset (Atom b)} (more : K a) (p : Path sys a k Γ b f k' Γ'),
    (strengthen more p).uses = p.uses
  | _, _, _, _, _, _, _, _, .done _ _ _ => rfl
  | _, _, _, _, _, _, _, _, .fire _ _ _ _ _ _ _ _ _ rest => by
      show _ :: (strengthen _ rest).uses = _ :: rest.uses
      rw [uses_strengthen]

theorem uses_leaf {a : Frame} (declaration : Rule a) (k : K a)
    (asked : sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)) :
    (leaf declaration k asked).uses = [⟨a, declaration⟩] :=
  rfl

/-! ### The fibred structural equations -/

theorem cut_assoc {a b c d : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k₁ : K b}
    {Γ₁ : Multiset (Atom b)} {g : b ⟶ c} {k₂ : K c} {Γ₂ : Multiset (Atom c)} {h : c ⟶ d}
    {k' : K d} {Γ' : Multiset (Atom d)} (p : Path sys a k Γ b f k₁ Γ₁) (q : Path sys b k₁ Γ₁ c g k₂ Γ₂)
    (r : Path sys c k₂ Γ₂ d h k' Γ') :
    cut (cut p q) r = recast (H := Path sys) rfl rfl (Category.assoc f g h).symm rfl rfl (cut p (cut q r)) :=
  eq_of_uses _ _ (by rw [uses_recast, uses_cut, uses_cut, uses_cut, uses_cut, List.append_assoc])

theorem done_cut {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (p : Path sys a k Γ b f k' Γ') :
    cut (identity a k Γ) p = recast (H := Path sys) rfl rfl (Category.id_comp f).symm rfl rfl p :=
  eq_of_uses _ _ (by rw [uses_recast, uses_cut]; rfl)

theorem cut_done {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (p : Path sys a k Γ b f k' Γ') :
    cut p (identity b k' Γ') = recast (H := Path sys) rfl rfl (Category.comp_id f).symm rfl rfl p :=
  eq_of_uses _ _ (by rw [uses_recast, uses_cut]; exact List.append_nil _)

theorem frame_zero {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (p : Path sys a k Γ b f k' Γ') :
    frame 0 p = recast (H := Path sys) rfl (add_zero Γ).symm rfl rfl
      (by rw [IndexedSystem.carried_zero, add_zero]) p :=
  eq_of_uses _ _ (by rw [uses_frame, uses_recast])

theorem frame_frame {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (first second : Multiset (Atom a)) (p : Path sys a k Γ b f k' Γ') :
    frame second (frame first p) = recast (H := Path sys) rfl (add_assoc Γ first second).symm rfl rfl
      (by rw [IndexedSystem.carried_add, add_assoc]) (frame (first + second) p) :=
  eq_of_uses _ _ (by rw [uses_frame, uses_frame, uses_recast, uses_frame])

/-- **Framing a cut frames its second part by the atoms carried along the first.** -/
theorem frame_cut {a b c : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k₁ : K b}
    {Γ₁ : Multiset (Atom b)} {g : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)} (extra : Multiset (Atom a))
    (p : Path sys a k Γ b f k₁ Γ₁) (q : Path sys b k₁ Γ₁ c g k' Γ') :
    frame extra (cut p q) = recast (H := Path sys) rfl rfl rfl rfl
      (by rw [IndexedSystem.carried_comp]) (cut (frame extra p) (frame (sys.carried f extra) q)) :=
  eq_of_uses _ _ (by rw [uses_frame, uses_recast, uses_cut, uses_cut, uses_frame, uses_frame])

theorem frame_done {a : Frame} (extra : Multiset (Atom a)) (k : K a) (Γ : Multiset (Atom a)) :
    frame extra (identity (sys := sys) a k Γ) = recast (H := Path sys) rfl rfl rfl rfl
      (by rw [IndexedSystem.carried_id]) (identity a k (Γ + extra)) :=
  eq_of_uses _ _ (by rw [uses_recast]; rfl)

theorem strengthen_leaf {a : Frame} (more : K a) (declaration : Rule a) (k : K a)
    (asked : sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)) :
    strengthen more (leaf declaration k asked) = recast (H := Path sys) rfl rfl rfl
      (by rw [sys.know_inf, inf_right_comm]) rfl
      (leaf declaration (k ⊓ more) (by
        rw [sys.know_inf]
        exact sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked)) :=
  eq_of_uses _ _ (by rw [uses_strengthen, uses_recast]; rfl)

theorem strengthen_done {a : Frame} (more : K a) (k : K a) (Γ : Multiset (Atom a)) :
    strengthen more (identity (sys := sys) a k Γ) = recast (H := Path sys) rfl rfl rfl
      (by rw [sys.know_id]) rfl (identity a (k ⊓ more) Γ) :=
  eq_of_uses _ _ (by rw [uses_recast]; rfl)

/-- **Strengthening a cut strengthens its second part by the knowledge transported along the first.** -/
theorem strengthen_cut {a b c : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k₁ : K b}
    {Γ₁ : Multiset (Atom b)} {g : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)} (more : K a)
    (p : Path sys a k Γ b f k₁ Γ₁) (q : Path sys b k₁ Γ₁ c g k' Γ') :
    strengthen more (cut p q) = recast (H := Path sys) rfl rfl rfl
      (by rw [sys.know_comp]) rfl (cut (strengthen more p) (strengthen (sys.know f more) q)) :=
  eq_of_uses _ _ (by
    rw [uses_strengthen, uses_recast, uses_cut, uses_cut, uses_strengthen, uses_strengthen])

theorem strengthen_frame {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (more : K a) (extra : Multiset (Atom a)) (p : Path sys a k Γ b f k' Γ') :
    strengthen more (frame extra p) = frame extra (strengthen more p) :=
  eq_of_uses _ _ (by rw [uses_strengthen, uses_frame, uses_frame, uses_strengthen])

end Path

/-! ## Proof-relevant models over frames -/

/-- **A proof-relevant model of the frame-indexed calculus**: morphisms over frame maps, the five
operations, and the fibred structural equations, each up to the equations of its indices. -/
structure FibredModel (sys : IndexedSystem Frame K Atom Rule) where
  Hom : (a : Frame) → K a → Multiset (Atom a) → (b : Frame) → (a ⟶ b) → K b → Multiset (Atom b) →
    Type uM
  identity : (a : Frame) → (k : K a) → (Γ : Multiset (Atom a)) → Hom a k Γ a (𝟙 a) k Γ
  rule : {a : Frame} → (declaration : Rule a) → (k : K a) →
    sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) →
    Hom a k (sys.premises declaration) (sys.target declaration) (sys.extend declaration)
      (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) (sys.conclusions declaration)
  frame : {a b : Frame} → {k : K a} → {Γ : Multiset (Atom a)} → {f : a ⟶ b} → {k' : K b} →
    {Γ' : Multiset (Atom b)} → (extra : Multiset (Atom a)) → Hom a k Γ b f k' Γ' →
    Hom a k (Γ + extra) b f k' (Γ' + sys.carried f extra)
  strengthen : {a b : Frame} → {k : K a} → {Γ : Multiset (Atom a)} → {f : a ⟶ b} → {k' : K b} →
    {Γ' : Multiset (Atom b)} → (more : K a) → Hom a k Γ b f k' Γ' →
    Hom a (k ⊓ more) Γ b f (k' ⊓ sys.know f more) Γ'
  cut : {a b c : Frame} → {k : K a} → {Γ : Multiset (Atom a)} → {f : a ⟶ b} → {k₁ : K b} →
    {Γ₁ : Multiset (Atom b)} → {g : b ⟶ c} → {k' : K c} → {Γ' : Multiset (Atom c)} →
    Hom a k Γ b f k₁ Γ₁ → Hom b k₁ Γ₁ c g k' Γ' → Hom a k Γ c (f ≫ g) k' Γ'
  cut_assoc : ∀ {a b c d : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k₁ : K b}
    {Γ₁ : Multiset (Atom b)} {g : b ⟶ c} {k₂ : K c} {Γ₂ : Multiset (Atom c)} {h : c ⟶ d}
    {k' : K d} {Γ' : Multiset (Atom d)} (p : Hom a k Γ b f k₁ Γ₁) (q : Hom b k₁ Γ₁ c g k₂ Γ₂)
    (r : Hom c k₂ Γ₂ d h k' Γ'),
    cut (cut p q) r = recast (H := Hom) rfl rfl (Category.assoc f g h).symm rfl rfl (cut p (cut q r))
  identity_cut : ∀ {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (p : Hom a k Γ b f k' Γ'),
    cut (identity a k Γ) p = recast (H := Hom) rfl rfl (Category.id_comp f).symm rfl rfl p
  cut_identity : ∀ {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (p : Hom a k Γ b f k' Γ'),
    cut p (identity b k' Γ') = recast (H := Hom) rfl rfl (Category.comp_id f).symm rfl rfl p
  frame_zero : ∀ {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (p : Hom a k Γ b f k' Γ'),
    frame 0 p = recast (H := Hom) rfl (add_zero Γ).symm rfl rfl
      (by rw [IndexedSystem.carried_zero, add_zero]) p
  frame_frame : ∀ {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (first second : Multiset (Atom a)) (p : Hom a k Γ b f k' Γ'),
    frame second (frame first p) = recast (H := Hom) rfl (add_assoc Γ first second).symm rfl rfl
      (by rw [IndexedSystem.carried_add, add_assoc]) (frame (first + second) p)
  frame_cut : ∀ {a b c : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k₁ : K b}
    {Γ₁ : Multiset (Atom b)} {g : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)}
    (extra : Multiset (Atom a)) (p : Hom a k Γ b f k₁ Γ₁) (q : Hom b k₁ Γ₁ c g k' Γ'),
    frame extra (cut p q) = recast (H := Hom) rfl rfl rfl rfl
      (by rw [IndexedSystem.carried_comp]) (cut (frame extra p) (frame (sys.carried f extra) q))
  frame_identity : ∀ (a : Frame) (extra : Multiset (Atom a)) (k : K a) (Γ : Multiset (Atom a)),
    frame extra (identity a k Γ) = recast (H := Hom) rfl rfl rfl rfl
      (by rw [IndexedSystem.carried_id]) (identity a k (Γ + extra))
  strengthen_rule : ∀ {a : Frame} (more : K a) (declaration : Rule a) (k : K a)
    (asked : sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)),
    strengthen more (rule declaration k asked) = recast (H := Hom) rfl rfl rfl
      (by rw [sys.know_inf, inf_right_comm]) rfl
      (rule declaration (k ⊓ more) (by
        rw [sys.know_inf]
        exact sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked))
  strengthen_identity : ∀ (a : Frame) (more : K a) (k : K a) (Γ : Multiset (Atom a)),
    strengthen more (identity a k Γ) = recast (H := Hom) rfl rfl rfl
      (by rw [sys.know_id]) rfl (identity a (k ⊓ more) Γ)
  strengthen_cut : ∀ {a b c : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k₁ : K b}
    {Γ₁ : Multiset (Atom b)} {g : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)} (more : K a)
    (p : Hom a k Γ b f k₁ Γ₁) (q : Hom b k₁ Γ₁ c g k' Γ'),
    strengthen more (cut p q) = recast (H := Hom) rfl rfl rfl
      (by rw [sys.know_comp]) rfl (cut (strengthen more p) (strengthen (sys.know f more) q))
  strengthen_frame : ∀ {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (more : K a) (extra : Multiset (Atom a)) (p : Hom a k Γ b f k' Γ'),
    strengthen more (frame extra p) = frame extra (strengthen more p)

/-- **A map of models over frames** keeps the five operations. -/
structure FibredModelMap {sys : IndexedSystem Frame K Atom Rule}
    (M : FibredModel.{uF, uH, uK, uAtom, uRule, uM} sys) (N : FibredModel.{uF, uH, uK, uAtom, uRule, uN} sys) where
  map : {a : Frame} → {k : K a} → {Γ : Multiset (Atom a)} → {b : Frame} → {f : a ⟶ b} → {k' : K b} →
    {Γ' : Multiset (Atom b)} → M.Hom a k Γ b f k' Γ' → N.Hom a k Γ b f k' Γ'
  map_identity : ∀ (a : Frame) (k : K a) (Γ : Multiset (Atom a)), map (M.identity a k Γ) = N.identity a k Γ
  map_rule : ∀ {a : Frame} (declaration : Rule a) (k : K a)
    (asked : sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)),
    map (M.rule declaration k asked) = N.rule declaration k asked
  map_frame : ∀ {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (extra : Multiset (Atom a)) (p : M.Hom a k Γ b f k' Γ'),
    map (M.frame extra p) = N.frame extra (map p)
  map_strengthen : ∀ {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (more : K a) (p : M.Hom a k Γ b f k' Γ'),
    map (M.strengthen more p) = N.strengthen more (map p)
  map_cut : ∀ {a b c : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k₁ : K b}
    {Γ₁ : Multiset (Atom b)} {g : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)}
    (p : M.Hom a k Γ b f k₁ Γ₁) (q : M.Hom b k₁ Γ₁ c g k' Γ'), map (M.cut p q) = N.cut (map p) (map q)

/-- **The witnessed runs over frames are a model.** -/
abbrev paths (sys : IndexedSystem Frame K Atom Rule) :
    FibredModel.{uF, uH, uK, uAtom, uRule, max uF uH uK uAtom uRule} sys where
  Hom := Path sys
  identity a k Γ := Path.identity a k Γ
  rule declaration k asked := Path.leaf declaration k asked
  frame extra p := Path.frame extra p
  strengthen more p := Path.strengthen more p
  cut p q := Path.cut p q
  cut_assoc p q r := Path.cut_assoc p q r
  identity_cut p := Path.done_cut p
  cut_identity p := Path.cut_done p
  frame_zero p := Path.frame_zero p
  frame_frame first second p := Path.frame_frame first second p
  frame_cut extra p q := Path.frame_cut extra p q
  frame_identity a extra k Γ := Path.frame_done (a := a) extra k Γ
  strengthen_rule more declaration k asked := Path.strengthen_leaf more declaration k asked
  strengthen_identity a more k Γ := Path.strengthen_done (a := a) more k Γ
  strengthen_cut more p q := Path.strengthen_cut more p q
  strengthen_frame more extra p := Path.strengthen_frame more extra p

/-! ## Transport lemmas -/

section Transport

variable {H : (a : Frame) → K a → Multiset (Atom a) → (b : Frame) → (a ⟶ b) → K b →
  Multiset (Atom b) → Type uM}

omit [∀ a, SemilatticeInf (K a)] in
theorem recast_self {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)} (hk : k = k) (hΓ : Γ = Γ) (hf : f = f) (hk' : k' = k') (hΓ' : Γ' = Γ')
    (x : H a k Γ b f k' Γ') : recast hk hΓ hf hk' hΓ' x = x :=
  rfl

omit [∀ a, SemilatticeInf (K a)] in
theorem recast_recast {a b : Frame} {k j i : K a} {Γ Δ Θ : Multiset (Atom a)} {f g h : a ⟶ b}
    {k' j' i' : K b} {Γ' Δ' Θ' : Multiset (Atom b)} (hk : k = j) (hΓ : Γ = Δ) (hf : f = g)
    (hk' : k' = j') (hΓ' : Γ' = Δ') (gk : j = i) (gΓ : Δ = Θ) (gf : g = h) (gk' : j' = i')
    (gΓ' : Δ' = Θ') (x : H a k Γ b f k' Γ') :
    recast gk gΓ gf gk' gΓ' (recast hk hΓ hf hk' hΓ' x) =
      recast (hk.trans gk) (hΓ.trans gΓ) (hf.trans gf) (hk'.trans gk') (hΓ'.trans gΓ') x := by
  subst hk hΓ hf hk' hΓ' gk gΓ gf gk' gΓ'
  rfl

omit [∀ a, SemilatticeInf (K a)] in
/-- A family of maps commutes with transport. -/
theorem map_recast {H' : (a : Frame) → K a → Multiset (Atom a) → (b : Frame) → (a ⟶ b) → K b →
      Multiset (Atom b) → Type uN}
    (map : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b}
      {Γ' : Multiset (Atom b)}, H a k Γ b f k' Γ' → H' a k Γ b f k' Γ')
    {a b : Frame} {k j : K a} {Γ Δ : Multiset (Atom a)} {f g : a ⟶ b} {k' j' : K b}
    {Γ' Δ' : Multiset (Atom b)} (hk : k = j) (hΓ : Γ = Δ) (hf : f = g) (hk' : k' = j')
    (hΓ' : Γ' = Δ') (x : H a k Γ b f k' Γ') :
    map (recast hk hΓ hf hk' hΓ' x) = recast hk hΓ hf hk' hΓ' (map x) := by
  subst hk hΓ hf hk' hΓ'
  rfl

end Transport

namespace FibredModel

variable {sys : IndexedSystem Frame K Atom Rule} (M : FibredModel.{uF, uH, uK, uAtom, uRule, uM} sys)

/-- A transport on the first part of a cut moves its change of the middle onto the second part. -/
theorem cut_recast_left {a b c : Frame} {k j : K a} {Γ Δ : Multiset (Atom a)} {f g : a ⟶ b}
    {k₁ j₁ : K b} {Γ₁ Δ₁ : Multiset (Atom b)} {h : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)}
    (hk : k = j) (hΓ : Γ = Δ) (hf : f = g) (hk₁ : k₁ = j₁) (hΓ₁ : Γ₁ = Δ₁)
    (p : M.Hom a k Γ b f k₁ Γ₁) (q : M.Hom b j₁ Δ₁ c h k' Γ') :
    M.cut (recast hk hΓ hf hk₁ hΓ₁ p) q =
      recast hk hΓ (by rw [hf]) rfl rfl (M.cut p (recast hk₁.symm hΓ₁.symm rfl rfl rfl q)) := by
  subst hk hΓ hf hk₁ hΓ₁
  rfl

theorem frame_recast {a b : Frame} {k j : K a} {Γ Δ : Multiset (Atom a)} {f g : a ⟶ b}
    {k' j' : K b} {Γ' Δ' : Multiset (Atom b)} (extra : Multiset (Atom a)) (hk : k = j)
    (hΓ : Γ = Δ) (hf : f = g) (hk' : k' = j') (hΓ' : Γ' = Δ') (x : M.Hom a k Γ b f k' Γ') :
    M.frame extra (recast hk hΓ hf hk' hΓ' x) =
      recast hk (by rw [hΓ]) hf hk' (by rw [hΓ', hf]) (M.frame extra x) := by
  subst hk hΓ hf hk' hΓ'
  rfl

end FibredModel

/-! ## Initiality over frames -/

section Initiality

variable {sys : IndexedSystem Frame K Atom Rule} (M : FibredModel.{uF, uH, uK, uAtom, uRule, uM} sys)

/-- **The interpretation of a witnessed run over frames**: the cut of its framed leaves. -/
def interp : ∀ {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b}
    {Γ' : Multiset (Atom b)}, Path sys a k Γ b f k' Γ' → M.Hom a k Γ b f k' Γ'
  | _, _, _, _, _, _, _, .done route told target =>
      recast (H := M.Hom) rfl rfl route.symm told.symm target.symm (M.identity _ _ _)
  | _, _, _, _, _, _, _, .fire declaration φ source asked told target route finalKnowledge finalAtoms
      rest =>
      recast (H := M.Hom) rfl source.symm route.symm finalKnowledge.symm finalAtoms.symm
        (M.cut (recast (H := M.Hom) rfl rfl rfl told.symm target.symm
          (M.frame φ (M.rule declaration _ asked))) (interp rest))

theorem interp_recast {a b : Frame} {k j : K a} {Γ Δ : Multiset (Atom a)} {f g : a ⟶ b}
    {k' j' : K b} {Γ' Δ' : Multiset (Atom b)} (hk : k = j) (hΓ : Γ = Δ) (hf : f = g)
    (hk' : k' = j') (hΓ' : Γ' = Δ') (p : Path sys a k Γ b f k' Γ') :
    interp M (recast (H := Path sys) hk hΓ hf hk' hΓ' p) =
      recast (H := M.Hom) hk hΓ hf hk' hΓ' (interp M p) := by
  subst hk hΓ hf hk' hΓ'
  rfl

theorem interp_cut {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b}
    {k₁ : K b} {Γ₁ : Multiset (Atom b)} (p : Path sys a k Γ b f k₁ Γ₁) :
    ∀ {c : Frame} {g : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)} (q : Path sys b k₁ Γ₁ c g k' Γ'),
      interp M (Path.cut p q) = M.cut (interp M p) (interp M q) := by
  induction p with
  | done route told target =>
      intro c g k' Γ' q
      subst route told target
      simp only [Path.cut, interp, interp_recast, recast_self]
      rw [M.identity_cut]
  | fire declaration φ source asked told target route finalKnowledge finalAtoms rest ih =>
      intro c g k' Γ' q
      subst source told target route finalKnowledge finalAtoms
      simp only [Path.cut, interp, ih, recast_self]
      rw [M.cut_assoc]

theorem interp_frame {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b}
    {k' : K b} {Γ' : Multiset (Atom b)} (p : Path sys a k Γ b f k' Γ') :
    ∀ extra : Multiset (Atom a), interp M (Path.frame extra p) = M.frame extra (interp M p) := by
  induction p with
  | done route told target =>
      intro extra
      subst route told target
      simp only [Path.frame, interp, recast_self]
      rw [M.frame_identity]
  | fire declaration φ source asked told target route finalKnowledge finalAtoms rest ih =>
      intro extra
      subst source told target route finalKnowledge finalAtoms
      simp only [Path.frame, interp, ih, recast_self]
      rw [M.frame_cut, M.frame_frame, M.cut_recast_left, M.cut_recast_left, recast_recast,
        recast_recast]

theorem interp_strengthen {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b}
    {k' : K b} {Γ' : Multiset (Atom b)} (p : Path sys a k Γ b f k' Γ') :
    ∀ more : K a, interp M (Path.strengthen more p) = M.strengthen more (interp M p) := by
  induction p with
  | done route told target =>
      intro more
      subst route told target
      simp only [Path.strengthen, interp, recast_self]
      rw [M.strengthen_identity]
  | fire declaration φ source asked told target route finalKnowledge finalAtoms rest ih =>
      intro more
      subst source told target route finalKnowledge finalAtoms
      simp only [Path.strengthen, interp, ih, recast_self]
      rw [M.strengthen_cut, M.strengthen_frame, M.strengthen_rule, M.frame_recast,
        M.cut_recast_left]

theorem interp_leaf {a : Frame} (declaration : Rule a) (k : K a)
    (asked : sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)) :
    interp M (Path.leaf declaration k asked) = M.rule declaration k asked := by
  simp only [Path.leaf, interp, recast_self]
  rw [M.cut_identity, M.frame_zero, recast_recast, recast_recast, recast_recast]
  rfl

/-- **The map from witnessed runs over frames** into a model. -/
def lift : FibredModelMap (paths sys) M where
  map p := interp M p
  map_identity _ _ _ := rfl
  map_rule declaration k asked := interp_leaf M declaration k asked
  map_frame extra p := interp_frame M p extra
  map_strengthen more p := interp_strengthen M p more
  map_cut p q := interp_cut M p q

/-- **Uniqueness**: every map of models from the witnessed runs over frames is the interpretation. -/
theorem lift_unique (F : FibredModelMap (paths sys) M) {a : Frame} {k : K a}
    {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (p : Path sys a k Γ b f k' Γ') : F.map p = interp M p := by
  induction p with
  | done route told target =>
      subst route told target
      exact F.map_identity _ _ _
  | fire declaration φ source asked told target route finalKnowledge finalAtoms rest ih =>
      have split : (Path.fire declaration φ source asked told target route finalKnowledge finalAtoms
          rest : Path sys _ _ _ _ _ _ _) =
          recast (H := Path sys) rfl source.symm route.symm finalKnowledge.symm finalAtoms.symm
            (Path.cut (recast (H := Path sys) rfl rfl rfl told.symm target.symm
              (Path.frame φ (Path.leaf declaration _ asked))) rest) :=
        Path.eq_of_uses _ _ (by
          rw [Path.uses_recast, Path.uses_cut, Path.uses_recast, Path.uses_frame]
          rfl)
      have mapped := congrArg (fun p => F.map p) split
      refine mapped.trans ?_
      rw [map_recast (H := Path sys) F.map]
      refine (congrArg (recast (H := M.Hom) _ _ _ _ _) (F.map_cut _ rest)).trans ?_
      rw [map_recast (H := Path sys) F.map, F.map_frame, F.map_rule, ih]
      rfl

/-- **The witnessed runs over frames are the initial proof-relevant model of the frame-indexed
calculus.** -/
theorem paths_initial :
    ∃ F : FibredModelMap (paths sys) M, ∀ (G : FibredModelMap (paths sys) M) {a : Frame} {k : K a}
      {Γ : Multiset (Atom a)} {b : Frame} {f : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
      (p : Path sys a k Γ b f k' Γ'), G.map p = F.map p :=
  ⟨lift M, fun G _ _ _ _ _ _ _ p => lift_unique M G p⟩

end Initiality

/-! ## The relational models over frames are the truncation -/

section Truncation

variable {sys : IndexedSystem Frame K Atom Rule}

/-- **A relational model of the frame-indexed calculus**: a relation on sequents over frame maps
closed under its five rules. -/
structure RelationalModel (sys : IndexedSystem Frame K Atom Rule)
    (holds : (a : Frame) → K a → Multiset (Atom a) → List (Sigma Rule) → (b : Frame) → (a ⟶ b) →
      K b → Multiset (Atom b) → Prop) : Prop where
  identity : ∀ (a : Frame) (k : K a) (Γ : Multiset (Atom a)), holds a k Γ [] a (𝟙 a) k Γ
  rule : ∀ {a : Frame} (declaration : Rule a) (k : K a),
    sys.guard declaration (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) →
    holds a k (sys.premises declaration) [⟨a, declaration⟩] (sys.target declaration)
      (sys.extend declaration) (sys.know (sys.extend declaration) k ⊓ sys.tell declaration)
      (sys.conclusions declaration)
  frame : ∀ {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)} {f : a ⟶ b}
    {k' : K b} {Γ' : Multiset (Atom b)} (extra : Multiset (Atom a)),
    holds a k Γ uses b f k' Γ' → holds a k (Γ + extra) uses b f k' (Γ' + sys.carried f extra)
  strengthen : ∀ {a b : Frame} {k : K a} {Γ : Multiset (Atom a)} {uses : List (Sigma Rule)}
    {f : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)} (more : K a),
    holds a k Γ uses b f k' Γ' → holds a (k ⊓ more) Γ uses b f (k' ⊓ sys.know f more) Γ'
  cut : ∀ {a b c : Frame} {k : K a} {Γ : Multiset (Atom a)} {first second : List (Sigma Rule)}
    {f : a ⟶ b} {k₁ : K b} {Γ₁ : Multiset (Atom b)} {g : b ⟶ c} {k' : K c} {Γ' : Multiset (Atom c)},
    holds a k Γ first b f k₁ Γ₁ → holds b k₁ Γ₁ second c g k' Γ' →
      holds a k Γ (first ++ second) c (f ≫ g) k' Γ'

/-- The words of a relation at a sequent over a frame map. -/
abbrev Words (holds : (a : Frame) → K a → Multiset (Atom a) → List (Sigma Rule) → (b : Frame) →
      (a ⟶ b) → K b → Multiset (Atom b) → Prop)
    (a : Frame) (k : K a) (Γ : Multiset (Atom a)) (b : Frame) (f : a ⟶ b) (k' : K b)
    (Γ' : Multiset (Atom b)) : Type (max uF uRule) :=
  {uses : List (Sigma Rule) // holds a k Γ uses b f k' Γ'}

omit [∀ a, SemilatticeInf (K a)] in
theorem val_recast {holds : (a : Frame) → K a → Multiset (Atom a) → List (Sigma Rule) → (b : Frame) →
      (a ⟶ b) → K b → Multiset (Atom b) → Prop}
    {a b : Frame} {k j : K a} {Γ Δ : Multiset (Atom a)} {f g : a ⟶ b} {k' j' : K b}
    {Γ' Δ' : Multiset (Atom b)} (hk : k = j) (hΓ : Γ = Δ) (hf : f = g) (hk' : k' = j')
    (hΓ' : Γ' = Δ') (x : Words holds a k Γ b f k' Γ') :
    (recast (H := Words holds) hk hΓ hf hk' hΓ' x).1 = x.1 := by
  subst hk hΓ hf hk' hΓ'
  rfl

/-- A relational model as a proof-relevant one: a morphism is a word for which the relation holds. -/
abbrev wordModel {holds : (a : Frame) → K a → Multiset (Atom a) → List (Sigma Rule) → (b : Frame) →
      (a ⟶ b) → K b → Multiset (Atom b) → Prop}
    (model : RelationalModel sys holds) : FibredModel.{uF, uH, uK, uAtom, uRule, max uF uRule} sys where
  Hom := Words holds
  identity a k Γ := ⟨[], model.identity a k Γ⟩
  rule declaration k asked := ⟨[⟨_, declaration⟩], model.rule declaration k asked⟩
  frame extra p := ⟨p.1, model.frame extra p.2⟩
  strengthen more p := ⟨p.1, model.strengthen more p.2⟩
  cut p q := ⟨p.1 ++ q.1, model.cut p.2 q.2⟩
  cut_assoc p q r := Subtype.ext ((List.append_assoc p.1 q.1 r.1).trans
    (val_recast _ _ _ _ _ (⟨p.1 ++ (q.1 ++ r.1), model.cut p.2 (model.cut q.2 r.2)⟩ :
      Words holds _ _ _ _ _ _ _)).symm)
  identity_cut p := Subtype.ext (val_recast _ _ _ _ _ p).symm
  cut_identity p := Subtype.ext ((List.append_nil p.1).trans (val_recast _ _ _ _ _ p).symm)
  frame_zero p := Subtype.ext (val_recast _ _ _ _ _ p).symm
  frame_frame first second p := Subtype.ext (val_recast _ _ _ _ _
    (⟨p.1, model.frame (first + second) p.2⟩ : Words holds _ _ _ _ _ _ _)).symm
  frame_cut extra p q := Subtype.ext (val_recast _ _ _ _ _
    (⟨p.1 ++ q.1, model.cut (model.frame extra p.2) (model.frame (sys.carried _ extra) q.2)⟩ :
      Words holds _ _ _ _ _ _ _)).symm
  frame_identity a extra k Γ := Subtype.ext (val_recast _ _ _ _ _
    (⟨[], model.identity a k (Γ + extra)⟩ : Words holds _ _ _ _ _ _ _)).symm
  strengthen_rule more declaration k asked := Subtype.ext (val_recast _ _ _ _ _
    (⟨[⟨_, declaration⟩], model.rule declaration (k ⊓ more) (by
      rw [sys.know_inf]
      exact sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked)⟩ :
      Words holds _ _ _ _ _ _ _)).symm
  strengthen_identity a more k Γ := Subtype.ext (val_recast _ _ _ _ _
    (⟨[], model.identity a (k ⊓ more) Γ⟩ : Words holds _ _ _ _ _ _ _)).symm
  strengthen_cut more p q := Subtype.ext (val_recast _ _ _ _ _
    (⟨p.1 ++ q.1, model.cut (model.strengthen more p.2) (model.strengthen (sys.know _ more) q.2)⟩ :
      Words holds _ _ _ _ _ _ _)).symm
  strengthen_frame _ _ _ := rfl

theorem interp_wordModel {holds : (a : Frame) → K a → Multiset (Atom a) → List (Sigma Rule) →
      (b : Frame) → (a ⟶ b) → K b → Multiset (Atom b) → Prop}
    (model : RelationalModel sys holds) {a : Frame} {k : K a} {Γ : Multiset (Atom a)} {b : Frame}
    {f : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)} (p : Path sys a k Γ b f k' Γ') :
    (interp (wordModel model) p).1 = p.uses := by
  induction p with
  | done route told target => exact val_recast _ _ _ _ _ _
  | fire declaration φ source asked told target route finalKnowledge finalAtoms rest ih =>
      show (recast (H := Words holds) _ _ _ _ _ (⟨(recast (H := Words holds) _ _ _ _ _
          (⟨[⟨_, declaration⟩], _⟩ : Words holds _ _ _ _ _ _ _)).1 ++ (interp (wordModel model) rest).1,
          _⟩ : Words holds _ _ _ _ _ _ _)).1 = ⟨_, declaration⟩ :: rest.uses
      rw [val_recast]
      change (recast (H := Words holds) _ _ _ _ _
          (⟨[⟨_, declaration⟩], _⟩ : Words holds _ _ _ _ _ _ _)).1 ++ (interp (wordModel model) rest).1 =
        ⟨_, declaration⟩ :: rest.uses
      rw [val_recast, ih]
      rfl

/-- **The relational initiality over frames is the truncation of the proof-relevant one**: every
run holds in every relational model. -/
theorem run_initial {holds : (a : Frame) → K a → Multiset (Atom a) → List (Sigma Rule) →
      (b : Frame) → (a ⟶ b) → K b → Multiset (Atom b) → Prop}
    (model : RelationalModel sys holds) {a : Frame} {k : K a} {Γ : Multiset (Atom a)}
    {uses : List (Sigma Rule)} {b : Frame} {f : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)}
    (run : sys.Run a k Γ uses b f k' Γ') : holds a k Γ uses b f k' Γ' := by
  obtain ⟨p, same⟩ := Path.exists_of_run run
  have image := (interp (wordModel model) p).2
  rw [interp_wordModel model p, same] at image
  exact image

/-- The runs are a relational model. -/
theorem runs_model : RelationalModel sys (fun a k Γ uses b f k' Γ' => sys.Run a k Γ uses b f k' Γ') where
  identity a k Γ := IndexedSystem.Run.done a k Γ
  rule declaration k asked := by
    have fires : sys.Fires declaration k (sys.premises declaration)
        (sys.know (sys.extend declaration) k ⊓ sys.tell declaration) (sys.conclusions declaration) :=
      ⟨0, (add_zero _).symm, asked, rfl, by rw [IndexedSystem.carried_zero, add_zero]⟩
    have run := IndexedSystem.Run.fire fires (IndexedSystem.Run.done _ _ _)
    rw [Category.comp_id] at run
    exact run
  frame extra run := IndexedSystem.Run.frame run extra
  strengthen more run := IndexedSystem.Run.strengthen run more
  cut one two := IndexedSystem.Run.append one two

/-- **A word runs over a frame map exactly when its sequent holds in every relational model.** -/
theorem run_iff_every_model {a : Frame} (k : K a) (Γ : Multiset (Atom a)) (uses : List (Sigma Rule))
    {b : Frame} (f : a ⟶ b) (k' : K b) (Γ' : Multiset (Atom b)) :
    sys.Run a k Γ uses b f k' Γ' ↔
      ∀ holds : (a : Frame) → K a → Multiset (Atom a) → List (Sigma Rule) → (b : Frame) →
          (a ⟶ b) → K b → Multiset (Atom b) → Prop,
        RelationalModel sys holds → holds a k Γ uses b f k' Γ' :=
  ⟨fun run _ model => run_initial model run, fun every => every _ runs_model⟩

end Truncation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Fibred
