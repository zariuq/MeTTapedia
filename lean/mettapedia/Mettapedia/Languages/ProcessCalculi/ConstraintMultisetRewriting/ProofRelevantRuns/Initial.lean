import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mettapedia.Logic.LinearLogic.KnowledgeTensorInitial
import Mettapedia.Logic.LinearLogic.KnowledgeTensorProofTerms

/-!
# Witnessed runs, and proof-relevant initiality

`KnowledgeTensorInitial` proves that the runs are the least relation closed under the five rules
of the two-zone calculus. A relation cannot say that an interpretation of runs is unique, and it
has room for at most one proof of a sequent. This module states the same initiality with
proof-relevant models.

* `Path`: a **witnessed run**. Each firing records its declaration, the frame of atoms it leaves
  untouched, its admission, and the state it leaves. `Path.run`, `Path.ofRun`: a witnessed run
  exists exactly where the run exists, with the same word. `Path.eq_of_uses`: a witnessed run is
  determined by its word, its source and its target.
* `RelevantModel`: a family of types of morphisms, indexed by sequents, with the five operations
  of the calculus (identity, rule, frame, strengthen, cut), satisfying exactly the structural
  equations of proof terms (`ProofTerm.Eqv`): cut is associative with the identity as unit,
  framing is an action of the frame monoid that commutes with cut, strengthening is an action of
  the knowledge meet that commutes with cut and with framing and is absorbed by a leaf.
* `paths`: the witnessed runs form a model, with cut the concatenation of firings.
* `lift`, `lift_unique`, `paths_initial`: **the witnessed runs are the initial proof-relevant
  model**: every model receives exactly one map that keeps the five operations.
* `wordModel`, `run_initial_of_relevant`: a relational model in the sense of
  `KnowledgeTensorInitial` is a proof-relevant model whose morphisms are its words, and
  `System.Run.initial` is recovered from the unique map into it.
* `weights`, `interp_weights`: a monoid with a weight for each declaration is a model, and the
  unique map sends a run to the product of the weights of its word, in its order.
* `eqv_iff_ofTyped_eq`: two proof terms of one sequent are equal modulo the structural equations
  exactly when they give the same witnessed run.

The laws of a model are exactly the generators of `ProofTerm.Eqv`; they are what makes the
interpretation of runs keep the operations. Index equations of the multisets and of the
knowledge are carried by `recast`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns

open Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule uM uN

/-! ## Transport along equations of the indices -/

section Recast

variable {K : Type uK} {Atom : Type uAtom}

/-- Transport of a sequent-indexed family along equations of its four indices. -/
def recast {H : K → Multiset Atom → K → Multiset Atom → Type uM} {k j k' j' : K}
    {Γ Δ Γ' Δ' : Multiset Atom} (hk : k = j) (hΓ : Γ = Δ) (hk' : k' = j') (hΓ' : Γ' = Δ')
    (x : H k Γ k' Γ') : H j Δ j' Δ' := by
  subst hk hΓ hk' hΓ'
  exact x

theorem recast_self {H : K → Multiset Atom → K → Multiset Atom → Type uM} {k k' : K}
    {Γ Γ' : Multiset Atom} (hk : k = k) (hΓ : Γ = Γ) (hk' : k' = k') (hΓ' : Γ' = Γ')
    (x : H k Γ k' Γ') : recast hk hΓ hk' hΓ' x = x :=
  rfl

theorem recast_recast {H : K → Multiset Atom → K → Multiset Atom → Type uM} {k j i k' j' i' : K}
    {Γ Δ Θ Γ' Δ' Θ' : Multiset Atom} (hk : k = j) (hΓ : Γ = Δ) (hk' : k' = j') (hΓ' : Γ' = Δ')
    (gk : j = i) (gΓ : Δ = Θ) (gk' : j' = i') (gΓ' : Δ' = Θ') (x : H k Γ k' Γ') :
    recast gk gΓ gk' gΓ' (recast hk hΓ hk' hΓ' x) =
      recast (hk.trans gk) (hΓ.trans gΓ) (hk'.trans gk') (hΓ'.trans gΓ') x := by
  subst hk hΓ hk' hΓ' gk gΓ gk' gΓ'
  rfl

/-- A family of maps between two sequent-indexed families commutes with transport. -/
theorem map_recast {H : K → Multiset Atom → K → Multiset Atom → Type uM}
    {H' : K → Multiset Atom → K → Multiset Atom → Type uN}
    (f : ∀ {k k' : K} {Γ Γ' : Multiset Atom}, H k Γ k' Γ' → H' k Γ k' Γ') {k j k' j' : K}
    {Γ Δ Γ' Δ' : Multiset Atom} (hk : k = j) (hΓ : Γ = Δ) (hk' : k' = j') (hΓ' : Γ' = Δ')
    (x : H k Γ k' Γ') : f (recast hk hΓ hk' hΓ' x) = recast hk hΓ hk' hΓ' (f x) := by
  subst hk hΓ hk' hΓ'
  rfl

/-- Transport in a constant family does nothing. -/
theorem recast_const {N : Type uM} {k j k' j' : K} {Γ Δ Γ' Δ' : Multiset Atom} (hk : k = j)
    (hΓ : Γ = Δ) (hk' : k' = j') (hΓ' : Γ' = Δ') (x : N) :
    recast (H := fun _ _ _ _ => N) hk hΓ hk' hΓ' x = x := by
  subst hk hΓ hk' hΓ'
  rfl

end Recast

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]

/-! ## Witnessed runs -/

/-- **A witnessed run.** Each firing records its declaration, the frame of atoms it leaves
untouched, its admission at the knowledge after its tell, and the state it leaves. -/
inductive Path (sys : System K Atom Rule) :
    K → Multiset Atom → K → Multiset Atom → Type (max uK uAtom uRule)
  | done (k : K) (Γ : Multiset Atom) : Path sys k Γ k Γ
  | fire {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} (declaration : Rule) (frame : Multiset Atom)
      (source : Γ = sys.premises declaration + frame)
      (asked : sys.guard declaration (k ⊓ sys.tell declaration))
      (told : k₁ = k ⊓ sys.tell declaration) (target : Γ₁ = sys.conclusions declaration + frame)
      (rest : Path sys k₁ Γ₁ k' Γ') : Path sys k Γ k' Γ'

namespace Path

variable {sys : System K Atom Rule}

/-- The word of a witnessed run. -/
def uses : ∀ {k k' : K} {Γ Γ' : Multiset Atom}, Path sys k Γ k' Γ' → List Rule
  | _, _, _, _, .done _ _ => []
  | _, _, _, _, .fire declaration _ _ _ _ _ rest => declaration :: uses rest

/-- The number of firings. -/
def length {k k' : K} {Γ Γ' : Multiset Atom} (p : Path sys k Γ k' Γ') : Nat := p.uses.length

/-- A witnessed run is a run of its word. -/
theorem run : ∀ {k k' : K} {Γ Γ' : Multiset Atom} (p : Path sys k Γ k' Γ'),
    sys.Run k Γ p.uses k' Γ'
  | _, _, _, _, .done k Γ => System.Run.done k Γ
  | _, _, _, _, .fire _ frame source asked told target rest =>
      System.Run.fire ⟨frame, source, asked, told, target⟩ (run rest)

theorem nil_inv {k k' : K} {Γ Γ' : Multiset Atom} (run : sys.Run k Γ [] k' Γ') : k = k' ∧ Γ = Γ' := by
  cases run
  exact ⟨rfl, rfl⟩

theorem cons_inv [DecidableEq Atom] {declaration : Rule} {rest : List Rule} {k k' : K}
    {Γ Γ' : Multiset Atom} (run : sys.Run k Γ (declaration :: rest) k' Γ') :
    Γ = sys.premises declaration + (Γ - sys.premises declaration) ∧
      sys.guard declaration (k ⊓ sys.tell declaration) ∧
      sys.Run (k ⊓ sys.tell declaration)
        (sys.conclusions declaration + (Γ - sys.premises declaration)) rest k' Γ' := by
  cases run with
  | fire fires later =>
      obtain ⟨frame, source, asked, told, target⟩ := fires
      subst source told target
      rw [add_tsub_cancel_left]
      exact ⟨rfl, asked, later⟩

/-- The witnessed run of a run: each frame is what the firing leaves untouched. -/
def ofRun [DecidableEq Atom] : ∀ (uses : List Rule) {k k' : K} {Γ Γ' : Multiset Atom},
    sys.Run k Γ uses k' Γ' → Path sys k Γ k' Γ'
  | [], k, _, Γ, _, run => recast rfl rfl (nil_inv run).1 (nil_inv run).2 (Path.done k Γ)
  | declaration :: rest, _, _, Γ, _, run =>
      Path.fire declaration (Γ - sys.premises declaration) (cons_inv run).1 (cons_inv run).2.1 rfl rfl
        (ofRun rest (cons_inv run).2.2)

theorem uses_recast {k j k' j' : K} {Γ Δ Γ' Δ' : Multiset Atom} (hk : k = j) (hΓ : Γ = Δ)
    (hk' : k' = j') (hΓ' : Γ' = Δ') (p : Path sys k Γ k' Γ') :
    (recast (H := Path sys) hk hΓ hk' hΓ' p).uses = p.uses := by
  subst hk hΓ hk' hΓ'
  rfl

theorem uses_ofRun [DecidableEq Atom] : ∀ (uses : List Rule) {k k' : K} {Γ Γ' : Multiset Atom}
    (run : sys.Run k Γ uses k' Γ'), (ofRun uses run).uses = uses
  | [], _, _, _, _, run => by
      show (recast (H := Path sys) rfl rfl _ _ (Path.done _ _)).uses = []
      rw [uses_recast]
      rfl
  | declaration :: rest, _, _, _, _, run => by
      show declaration :: (ofRun rest _).uses = declaration :: rest
      rw [uses_ofRun rest]

/-- **A witnessed run is determined by its word**, its source and its target. -/
theorem eq_of_uses {k k' : K} {Γ Γ' : Multiset Atom} (p q : Path sys k Γ k' Γ') :
    p.uses = q.uses → p = q := by
  induction p with
  | done k Γ =>
      intro same
      cases q with
      | done => rfl
      | fire => exact absurd same (List.cons_ne_nil _ _).symm
  | fire declaration frame source asked told target rest ih =>
      intro same
      cases q with
      | done => exact absurd same (List.cons_ne_nil _ _)
      | fire declaration' frame' source' asked' told' target' rest' =>
          have words : declaration :: rest.uses = declaration' :: rest'.uses := same
          obtain ⟨rfl, later⟩ := List.cons.inj words
          obtain rfl : frame = frame' := add_left_cancel (source.symm.trans source')
          subst told told' target target'
          rw [ih rest' later]

/-- **Witnessed runs exist exactly where runs exist**, with the same word. -/
theorem exists_iff_run [DecidableEq Atom] (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    (∃ p : Path sys k Γ k' Γ', p.uses = uses) ↔ sys.Run k Γ uses k' Γ' :=
  ⟨fun ⟨p, same⟩ => same ▸ p.run, fun run => ⟨ofRun uses run, uses_ofRun uses run⟩⟩

/-! ### The operations on witnessed runs -/

/-- Framing a witnessed run: every firing leaves the extra atoms untouched. -/
def frame (extra : Multiset Atom) : ∀ {k k' : K} {Γ Γ' : Multiset Atom},
    Path sys k Γ k' Γ' → Path sys k (Γ + extra) k' (Γ' + extra)
  | _, _, _, _, .done k Γ => .done k (Γ + extra)
  | _, _, _, _, .fire declaration φ source asked told target rest =>
      .fire declaration (φ + extra) (by rw [source, add_assoc]) asked told
        (by rw [target, add_assoc]) (frame extra rest)

/-- Strengthening a witnessed run: every firing is asked at more knowledge. -/
def strengthen (more : K) : ∀ {k k' : K} {Γ Γ' : Multiset Atom},
    Path sys k Γ k' Γ' → Path sys (k ⊓ more) Γ (k' ⊓ more) Γ'
  | _, _, _, _, .done k Γ => .done (k ⊓ more) Γ
  | _, _, _, _, .fire declaration φ source asked told target rest =>
      .fire declaration φ source (sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked)
        (by rw [told, inf_right_comm]) target (strengthen more rest)

/-- Cut: one witnessed run after another. -/
def cut : ∀ {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom},
    Path sys k Γ k₁ Γ₁ → Path sys k₁ Γ₁ k' Γ' → Path sys k Γ k' Γ'
  | _, _, _, _, _, _, .done _ _, q => q
  | _, _, _, _, _, _, .fire declaration φ source asked told target rest, q =>
      .fire declaration φ source asked told target (cut rest q)

/-- The witnessed run of one use of a declaration over nothing else. -/
def leaf (declaration : Rule) (k : K) (asked : sys.guard declaration (k ⊓ sys.tell declaration)) :
    Path sys k (sys.premises declaration) (k ⊓ sys.tell declaration) (sys.conclusions declaration) :=
  .fire declaration 0 (add_zero _).symm asked rfl (add_zero _).symm (.done _ _)

theorem uses_frame (extra : Multiset Atom) : ∀ {k k' : K} {Γ Γ' : Multiset Atom}
    (p : Path sys k Γ k' Γ'), (frame extra p).uses = p.uses
  | _, _, _, _, .done _ _ => rfl
  | _, _, _, _, .fire declaration _ _ _ _ _ rest =>
      congrArg (declaration :: ·) (uses_frame extra rest)

theorem uses_strengthen (more : K) : ∀ {k k' : K} {Γ Γ' : Multiset Atom}
    (p : Path sys k Γ k' Γ'), (strengthen more p).uses = p.uses
  | _, _, _, _, .done _ _ => rfl
  | _, _, _, _, .fire declaration _ _ _ _ _ rest =>
      congrArg (declaration :: ·) (uses_strengthen more rest)

theorem uses_cut : ∀ {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} (p : Path sys k Γ k₁ Γ₁)
    (q : Path sys k₁ Γ₁ k' Γ'), (cut p q).uses = p.uses ++ q.uses
  | _, _, _, _, _, _, .done _ _, _ => rfl
  | _, _, _, _, _, _, .fire declaration _ _ _ _ _ rest, q =>
      congrArg (declaration :: ·) (uses_cut rest q)

theorem uses_leaf (declaration : Rule) (k : K)
    (asked : sys.guard declaration (k ⊓ sys.tell declaration)) :
    (leaf declaration k asked).uses = [declaration] :=
  rfl

/-! ### The structural equations hold for witnessed runs -/

theorem cut_assoc {k k₁ k₂ k' : K} {Γ Γ₁ Γ₂ Γ' : Multiset Atom} (p : Path sys k Γ k₁ Γ₁)
    (q : Path sys k₁ Γ₁ k₂ Γ₂) (r : Path sys k₂ Γ₂ k' Γ') : cut (cut p q) r = cut p (cut q r) :=
  eq_of_uses _ _ (by rw [uses_cut, uses_cut, uses_cut, uses_cut, List.append_assoc])

theorem cut_done {k k' : K} {Γ Γ' : Multiset Atom} (p : Path sys k Γ k' Γ') :
    cut p (done k' Γ') = p :=
  eq_of_uses _ _ (by rw [uses_cut]; exact List.append_nil _)

theorem frame_zero {k k' : K} {Γ Γ' : Multiset Atom} (p : Path sys k Γ k' Γ') :
    frame 0 p = recast (H := Path sys) rfl (add_zero Γ).symm rfl (add_zero Γ').symm p :=
  eq_of_uses _ _ (by rw [uses_frame, uses_recast])

theorem frame_frame {k k' : K} {Γ Γ' : Multiset Atom} (first second : Multiset Atom)
    (p : Path sys k Γ k' Γ') : frame second (frame first p) =
      recast (H := Path sys) rfl (add_assoc Γ first second).symm rfl (add_assoc Γ' first second).symm
        (frame (first + second) p) :=
  eq_of_uses _ _ (by rw [uses_frame, uses_frame, uses_recast, uses_frame])

theorem frame_cut {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} (extra : Multiset Atom)
    (p : Path sys k Γ k₁ Γ₁) (q : Path sys k₁ Γ₁ k' Γ') :
    frame extra (cut p q) = cut (frame extra p) (frame extra q) :=
  eq_of_uses _ _ (by rw [uses_frame, uses_cut, uses_cut, uses_frame, uses_frame])

theorem strengthen_leaf (more : K) (declaration : Rule) (k : K)
    (asked : sys.guard declaration (k ⊓ sys.tell declaration)) :
    strengthen more (leaf declaration k asked) =
      recast (H := Path sys) rfl rfl (inf_right_comm k more (sys.tell declaration)) rfl
        (leaf declaration (k ⊓ more)
          (sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked)) :=
  eq_of_uses _ _ (by rw [uses_strengthen, uses_recast]; rfl)

theorem strengthen_cut {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} (more : K) (p : Path sys k Γ k₁ Γ₁)
    (q : Path sys k₁ Γ₁ k' Γ') : strengthen more (cut p q) = cut (strengthen more p) (strengthen more q) :=
  eq_of_uses _ _ (by rw [uses_strengthen, uses_cut, uses_cut, uses_strengthen, uses_strengthen])

theorem strengthen_frame {k k' : K} {Γ Γ' : Multiset Atom} (more : K) (extra : Multiset Atom)
    (p : Path sys k Γ k' Γ') : strengthen more (frame extra p) = frame extra (strengthen more p) :=
  eq_of_uses _ _ (by rw [uses_strengthen, uses_frame, uses_frame, uses_strengthen])

end Path

/-! ## Proof-relevant models -/

/-- **A proof-relevant model of the two-zone calculus.** Morphisms are indexed by sequents; the
five operations are those of the calculus, and the laws are exactly the generators of the
structural equations `ProofTerm.Eqv`. -/
structure RelevantModel (sys : System K Atom Rule) where
  Hom : K → Multiset Atom → K → Multiset Atom → Type uM
  identity : (k : K) → (Γ : Multiset Atom) → Hom k Γ k Γ
  rule : (declaration : Rule) → (k : K) → sys.guard declaration (k ⊓ sys.tell declaration) →
    Hom k (sys.premises declaration) (k ⊓ sys.tell declaration) (sys.conclusions declaration)
  frame : {k k' : K} → {Γ Γ' : Multiset Atom} → (extra : Multiset Atom) → Hom k Γ k' Γ' →
    Hom k (Γ + extra) k' (Γ' + extra)
  strengthen : {k k' : K} → {Γ Γ' : Multiset Atom} → (more : K) → Hom k Γ k' Γ' →
    Hom (k ⊓ more) Γ (k' ⊓ more) Γ'
  cut : {k k₁ k' : K} → {Γ Γ₁ Γ' : Multiset Atom} → Hom k Γ k₁ Γ₁ → Hom k₁ Γ₁ k' Γ' →
    Hom k Γ k' Γ'
  cut_assoc : ∀ {k k₁ k₂ k' : K} {Γ Γ₁ Γ₂ Γ' : Multiset Atom} (p : Hom k Γ k₁ Γ₁)
    (q : Hom k₁ Γ₁ k₂ Γ₂) (r : Hom k₂ Γ₂ k' Γ'), cut (cut p q) r = cut p (cut q r)
  identity_cut : ∀ {k k' : K} {Γ Γ' : Multiset Atom} (p : Hom k Γ k' Γ'), cut (identity k Γ) p = p
  cut_identity : ∀ {k k' : K} {Γ Γ' : Multiset Atom} (p : Hom k Γ k' Γ'), cut p (identity k' Γ') = p
  frame_zero : ∀ {k k' : K} {Γ Γ' : Multiset Atom} (p : Hom k Γ k' Γ'),
    frame 0 p = recast (H := Hom) rfl (add_zero Γ).symm rfl (add_zero Γ').symm p
  frame_frame : ∀ {k k' : K} {Γ Γ' : Multiset Atom} (first second : Multiset Atom)
    (p : Hom k Γ k' Γ'), frame second (frame first p) =
      recast (H := Hom) rfl (add_assoc Γ first second).symm rfl (add_assoc Γ' first second).symm
        (frame (first + second) p)
  frame_cut : ∀ {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} (extra : Multiset Atom)
    (p : Hom k Γ k₁ Γ₁) (q : Hom k₁ Γ₁ k' Γ'), frame extra (cut p q) = cut (frame extra p) (frame extra q)
  frame_identity : ∀ (extra : Multiset Atom) (k : K) (Γ : Multiset Atom),
    frame extra (identity k Γ) = identity k (Γ + extra)
  strengthen_rule : ∀ (more : K) (declaration : Rule) (k : K)
    (asked : sys.guard declaration (k ⊓ sys.tell declaration)),
    strengthen more (rule declaration k asked) =
      recast (H := Hom) rfl rfl (inf_right_comm k more (sys.tell declaration)) rfl
        (rule declaration (k ⊓ more)
          (sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked))
  strengthen_identity : ∀ (more : K) (k : K) (Γ : Multiset Atom),
    strengthen more (identity k Γ) = identity (k ⊓ more) Γ
  strengthen_cut : ∀ {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} (more : K) (p : Hom k Γ k₁ Γ₁)
    (q : Hom k₁ Γ₁ k' Γ'), strengthen more (cut p q) = cut (strengthen more p) (strengthen more q)
  strengthen_frame : ∀ {k k' : K} {Γ Γ' : Multiset Atom} (more : K) (extra : Multiset Atom)
    (p : Hom k Γ k' Γ'), strengthen more (frame extra p) = frame extra (strengthen more p)

/-- **A map of proof-relevant models** keeps the five operations. -/
structure ModelMap {sys : System K Atom Rule} (M : RelevantModel.{uK, uAtom, uRule, uM} sys)
    (N : RelevantModel.{uK, uAtom, uRule, uN} sys) where
  map : {k k' : K} → {Γ Γ' : Multiset Atom} → M.Hom k Γ k' Γ' → N.Hom k Γ k' Γ'
  map_identity : ∀ (k : K) (Γ : Multiset Atom), map (M.identity k Γ) = N.identity k Γ
  map_rule : ∀ (declaration : Rule) (k : K) (asked : sys.guard declaration (k ⊓ sys.tell declaration)),
    map (M.rule declaration k asked) = N.rule declaration k asked
  map_frame : ∀ {k k' : K} {Γ Γ' : Multiset Atom} (extra : Multiset Atom) (p : M.Hom k Γ k' Γ'),
    map (M.frame extra p) = N.frame extra (map p)
  map_strengthen : ∀ {k k' : K} {Γ Γ' : Multiset Atom} (more : K) (p : M.Hom k Γ k' Γ'),
    map (M.strengthen more p) = N.strengthen more (map p)
  map_cut : ∀ {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} (p : M.Hom k Γ k₁ Γ₁)
    (q : M.Hom k₁ Γ₁ k' Γ'), map (M.cut p q) = N.cut (map p) (map q)

namespace RelevantModel

variable {sys : System K Atom Rule} (M : RelevantModel.{uK, uAtom, uRule, uM} sys)

theorem frame_recast {k j k' j' : K} {Γ Δ Γ' Δ' : Multiset Atom} (extra : Multiset Atom)
    (hk : k = j) (hΓ : Γ = Δ) (hk' : k' = j') (hΓ' : Γ' = Δ') (x : M.Hom k Γ k' Γ') :
    M.frame extra (recast hk hΓ hk' hΓ' x) =
      recast hk (congrArg (· + extra) hΓ) hk' (congrArg (· + extra) hΓ') (M.frame extra x) := by
  subst hk hΓ hk' hΓ'
  rfl

theorem strengthen_recast {k j k' j' : K} {Γ Δ Γ' Δ' : Multiset Atom} (more : K)
    (hk : k = j) (hΓ : Γ = Δ) (hk' : k' = j') (hΓ' : Γ' = Δ') (x : M.Hom k Γ k' Γ') :
    M.strengthen more (recast hk hΓ hk' hΓ' x) =
      recast (congrArg (· ⊓ more) hk) hΓ (congrArg (· ⊓ more) hk') hΓ' (M.strengthen more x) := by
  subst hk hΓ hk' hΓ'
  rfl

end RelevantModel

/-! ## The witnessed runs are a model -/

/-- **The model of witnessed runs**: cut concatenates the firings, framing and strengthening act
firing by firing. Its laws hold because a witnessed run is determined by its word. -/
abbrev paths (sys : System K Atom Rule) : RelevantModel.{uK, uAtom, uRule, max uK uAtom uRule} sys where
  Hom := Path sys
  identity k Γ := Path.done k Γ
  rule declaration k asked := Path.leaf declaration k asked
  frame extra p := Path.frame extra p
  strengthen more p := Path.strengthen more p
  cut p q := Path.cut p q
  cut_assoc p q r := Path.cut_assoc p q r
  identity_cut _ := rfl
  cut_identity p := Path.cut_done p
  frame_zero p := Path.frame_zero p
  frame_frame first second p := Path.frame_frame first second p
  frame_cut extra p q := Path.frame_cut extra p q
  frame_identity _ _ _ := rfl
  strengthen_rule more declaration k asked := Path.strengthen_leaf more declaration k asked
  strengthen_identity _ _ _ := rfl
  strengthen_cut more p q := Path.strengthen_cut more p q
  strengthen_frame more extra p := Path.strengthen_frame more extra p

/-! ## Initiality -/

section Initiality

variable {sys : System K Atom Rule} (M : RelevantModel.{uK, uAtom, uRule, uM} sys)

/-- **The interpretation of a witnessed run**: the cut of its framed leaves, in order. -/
def interp : ∀ {k k' : K} {Γ Γ' : Multiset Atom}, Path sys k Γ k' Γ' → M.Hom k Γ k' Γ'
  | _, _, _, _, .done k Γ => M.identity k Γ
  | _, _, _, _, .fire declaration φ source asked told target rest =>
      M.cut (recast rfl source.symm told.symm target.symm (M.frame φ (M.rule declaration _ asked)))
        (interp rest)

theorem interp_cut : ∀ {k k₁ k' : K} {Γ Γ₁ Γ' : Multiset Atom} (p : Path sys k Γ k₁ Γ₁)
    (q : Path sys k₁ Γ₁ k' Γ'), interp M (Path.cut p q) = M.cut (interp M p) (interp M q)
  | _, _, _, _, _, _, .done _ _, _ => (M.identity_cut _).symm
  | _, _, _, _, _, _, .fire declaration φ source asked told target rest, q => by
      simp only [Path.cut, interp]
      rw [interp_cut rest q, M.cut_assoc]

theorem interp_frame (extra : Multiset Atom) : ∀ {k k' : K} {Γ Γ' : Multiset Atom}
    (p : Path sys k Γ k' Γ'), interp M (Path.frame extra p) = M.frame extra (interp M p)
  | _, _, _, _, .done k Γ => (M.frame_identity extra k Γ).symm
  | _, _, _, _, .fire declaration φ source asked told target rest => by
      simp only [Path.frame, interp]
      rw [interp_frame extra rest, M.frame_cut, M.frame_recast, M.frame_frame, recast_recast]

theorem interp_strengthen (more : K) : ∀ {k k' : K} {Γ Γ' : Multiset Atom}
    (p : Path sys k Γ k' Γ'), interp M (Path.strengthen more p) = M.strengthen more (interp M p)
  | _, _, _, _, .done k Γ => (M.strengthen_identity more k Γ).symm
  | _, _, _, _, .fire declaration φ source asked told target rest => by
      simp only [Path.strengthen, interp]
      rw [interp_strengthen more rest, M.strengthen_cut, M.strengthen_recast, M.strengthen_frame,
        M.strengthen_rule, M.frame_recast, recast_recast]

theorem interp_leaf (declaration : Rule) (k : K)
    (asked : sys.guard declaration (k ⊓ sys.tell declaration)) :
    interp M (Path.leaf declaration k asked) = M.rule declaration k asked := by
  simp only [Path.leaf, interp]
  rw [M.cut_identity, M.frame_zero, recast_recast]
  rfl

/-- **The map from witnessed runs** into a model. -/
def lift : ModelMap (paths sys) M where
  map p := interp M p
  map_identity _ _ := rfl
  map_rule declaration k asked := interp_leaf M declaration k asked
  map_frame extra p := interp_frame M extra p
  map_strengthen more p := interp_strengthen M more p
  map_cut p q := interp_cut M p q

/-- **Uniqueness**: every map of models from the witnessed runs is the interpretation. -/
theorem lift_unique (F : ModelMap (paths sys) M) : ∀ {k k' : K} {Γ Γ' : Multiset Atom}
    (p : Path sys k Γ k' Γ'), F.map p = interp M p
  | _, _, _, _, .done k Γ => F.map_identity k Γ
  | _, _, _, _, .fire declaration φ source asked told target rest => by
      have split : (Path.fire declaration φ source asked told target rest : Path sys _ _ _ _) =
          Path.cut (recast (H := Path sys) rfl source.symm told.symm target.symm
            (Path.frame φ (Path.leaf declaration _ asked))) rest :=
        Path.eq_of_uses _ _ (by
          rw [Path.uses_cut, Path.uses_recast, Path.uses_frame]
          rfl)
      have mapped := congrArg (fun p => F.map p) split
      refine mapped.trans ((F.map_cut _ rest).trans ?_)
      rw [map_recast (H := Path sys) F.map, F.map_frame, F.map_rule, lift_unique F rest]
      rfl

/-- **The witnessed runs are the initial proof-relevant model**: every model receives a map of
models from them, and any two such maps agree. -/
theorem paths_initial :
    ∃ F : ModelMap (paths sys) M, ∀ (G : ModelMap (paths sys) M) {k k' : K} {Γ Γ' : Multiset Atom}
      (p : Path sys k Γ k' Γ'), G.map p = F.map p :=
  ⟨lift M, fun G _ _ _ _ p => lift_unique M G p⟩

end Initiality

/-! ## The relational models are the truncation -/

section Truncation

variable {sys : System K Atom Rule}

/-- The words of a relation at a sequent. -/
abbrev Words (holds : K → Multiset Atom → List Rule → K → Multiset Atom → Prop) (k : K)
    (Γ : Multiset Atom) (k' : K) (Γ' : Multiset Atom) : Type uRule :=
  {uses : List Rule // holds k Γ uses k' Γ'}

omit [SemilatticeInf K] in
theorem val_recast {holds : K → Multiset Atom → List Rule → K → Multiset Atom → Prop}
    {k j k' j' : K} {Γ Δ Γ' Δ' : Multiset Atom} (hk : k = j) (hΓ : Γ = Δ) (hk' : k' = j')
    (hΓ' : Γ' = Δ') (x : Words holds k Γ k' Γ') :
    (recast (H := Words holds) hk hΓ hk' hΓ' x).1 = x.1 := by
  subst hk hΓ hk' hΓ'
  rfl

/-- A relational model as a proof-relevant one: a morphism is a word for which the relation holds. -/
abbrev wordModel {holds : K → Multiset Atom → List Rule → K → Multiset Atom → Prop}
    (model : sys.Model holds) : RelevantModel.{uK, uAtom, uRule, uRule} sys where
  Hom := Words holds
  identity k Γ := ⟨[], model.identity k Γ⟩
  rule declaration k asked := ⟨[declaration], model.rule declaration k asked⟩
  frame extra p := ⟨p.1, model.frame extra p.2⟩
  strengthen more p := ⟨p.1, model.strengthen more p.2⟩
  cut p q := ⟨p.1 ++ q.1, model.cut p.2 q.2⟩
  cut_assoc p q r := Subtype.ext (List.append_assoc p.1 q.1 r.1)
  identity_cut _ := rfl
  cut_identity p := Subtype.ext (List.append_nil p.1)
  frame_zero p := Subtype.ext (val_recast _ _ _ _ p).symm
  frame_frame first second p :=
    Subtype.ext (val_recast _ _ _ _ (⟨p.1, model.frame (first + second) p.2⟩ : Words holds _ _ _ _)).symm
  frame_cut _ _ _ := rfl
  frame_identity _ _ _ := rfl
  strengthen_rule more declaration k asked :=
    Subtype.ext (val_recast _ _ _ _ (⟨[declaration], model.rule declaration (k ⊓ more)
      (sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked)⟩ : Words holds _ _ _ _)).symm
  strengthen_identity _ _ _ := rfl
  strengthen_cut _ _ _ := rfl
  strengthen_frame _ _ _ := rfl

theorem interp_wordModel {holds : K → Multiset Atom → List Rule → K → Multiset Atom → Prop}
    (model : sys.Model holds) : ∀ {k k' : K} {Γ Γ' : Multiset Atom} (p : Path sys k Γ k' Γ'),
    (interp (wordModel model) p).1 = p.uses
  | _, _, _, _, .done _ _ => rfl
  | _, _, _, _, .fire declaration φ source asked told target rest => by
      show (recast (H := Words holds) rfl source.symm told.symm target.symm
          (⟨[declaration], _⟩ : Words holds _ _ _ _)).1 ++
          (interp (wordModel model) rest).1 = declaration :: rest.uses
      rw [val_recast, interp_wordModel model rest]
      rfl

/-- **The relational initiality is the truncation of the proof-relevant one**: `System.Run.initial`
follows from the map of witnessed runs into the model of words of a relation. -/
theorem run_initial_of_relevant {holds : K → Multiset Atom → List Rule → K → Multiset Atom → Prop}
    (model : sys.Model holds) {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.Run k Γ uses k' Γ') : holds k Γ uses k' Γ' := by
  classical
  have image := (interp (wordModel model) (Path.ofRun uses run)).2
  rw [interp_wordModel model, Path.uses_ofRun] at image
  exact image

end Truncation

/-! ## Weights -/

section Weights

variable {sys : System K Atom Rule}

/-- **A monoid of weights is a model**: a morphism is an element, cut multiplies, and framing and
strengthening keep it. -/
abbrev weights (N : Type uM) [Monoid N] (weight : Rule → N) : RelevantModel.{uK, uAtom, uRule, uM} sys where
  Hom _ _ _ _ := N
  identity _ _ := 1
  rule declaration _ _ := weight declaration
  frame _ x := x
  strengthen _ x := x
  cut x y := x * y
  cut_assoc x y z := mul_assoc x y z
  identity_cut x := one_mul x
  cut_identity x := mul_one x
  frame_zero x := (recast_const _ _ _ _ x).symm
  frame_frame _ _ x := (recast_const _ _ _ _ x).symm
  frame_cut _ _ _ := rfl
  frame_identity _ _ _ := rfl
  strengthen_rule _ declaration _ _ := (recast_const _ _ _ _ (weight declaration)).symm
  strengthen_identity _ _ _ := rfl
  strengthen_cut _ _ _ := rfl
  strengthen_frame _ _ _ := rfl

/-- **The weight of a witnessed run** is the product of the weights of its word, in order. -/
theorem interp_weights (N : Type uM) [Monoid N] (weight : Rule → N) :
    ∀ {k k' : K} {Γ Γ' : Multiset Atom} (p : Path sys k Γ k' Γ'),
      interp (weights (sys := sys) N weight) p = (p.uses.map weight).prod
  | _, _, _, _, .done _ _ => rfl
  | _, _, _, _, .fire declaration φ source asked told target rest => by
      show recast (H := fun _ _ _ _ => N) rfl source.symm told.symm target.symm (weight declaration) *
          (interp (weights (sys := sys) N weight) rest : N) =
            (weight declaration :: rest.uses.map weight).prod
      rw [recast_const, interp_weights N weight rest, List.prod_cons]

/-- Every map of models into a monoid of weights is the product of the weights. -/
theorem weights_unique (N : Type uM) [Monoid N] (weight : Rule → N)
    (F : ModelMap (paths sys) (weights (sys := sys) N weight)) {k k' : K} {Γ Γ' : Multiset Atom}
    (p : Path sys k Γ k' Γ') : F.map p = (p.uses.map weight).prod :=
  (lift_unique _ F p).trans (interp_weights N weight p)

end Weights

/-! ## Proof terms modulo the structural equations -/

section ProofTerms

variable {sys : System K Atom Rule} [DecidableEq Atom]

/-- The witnessed run of a typed proof term. -/
def ofTyped {p : ProofTerm K Atom Rule} {k k' : K} {Γ Γ' : Multiset Atom}
    (typed : sys.Typed p k Γ k' Γ') : Path sys k Γ k' Γ' :=
  Path.ofRun p.readout (System.Derives.run typed.derives)

theorem uses_ofTyped {p : ProofTerm K Atom Rule} {k k' : K} {Γ Γ' : Multiset Atom}
    (typed : sys.Typed p k Γ k' Γ') : (ofTyped typed).uses = p.readout :=
  Path.uses_ofRun _ _

/-- **Two proof terms of one sequent are equal modulo the structural equations exactly when they
give the same witnessed run.** -/
theorem eqv_iff_ofTyped_eq {p q : ProofTerm K Atom Rule} {k k' : K} {Γ Γ' : Multiset Atom}
    (first : sys.Typed p k Γ k' Γ') (second : sys.Typed q k Γ k' Γ') :
    ProofTerm.Eqv p q ↔ ofTyped first = ofTyped second := by
  rw [System.eqv_iff_readout first second]
  constructor
  · intro same
    exact Path.eq_of_uses _ _ (by rw [uses_ofTyped, uses_ofTyped, same])
  · intro same
    rw [← uses_ofTyped first, ← uses_ofTyped second, same]

end ProofTerms

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns
