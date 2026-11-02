import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommutativeMatching

/-!
# Region keys from types: sound modulo the theory by construction

A static footprint names regions by **keys**, and its guarantees need the keys to be sound for the
theory `E`: every value a pattern solves modulo `E` must be covered by the pattern's keys
(`Sources.RegionKeys.Sound`). Keys read off the syntax, such as head symbols or path prefixes, are
sound only when `E` preserves what they read; a prefix key must be widened under commutativity.

Types give keys that are sound by construction. A **classification** of values (`Classing`)
assigns each value a class (its sort, its type, the channel it lies at) that `E` preserves, and
assigns a pattern a class when every instance of the pattern has it. Its keys are the class of the
pattern, or "anywhere" when the pattern has no class.

* **Class keys are sound modulo `E`** (`classKeys_sound`), for every theory that preserves the
  classes. The proof uses only that equations relate values of one class: a sorted presentation
  has this property for its sorts, so sort keys are sound for every sorted theory.
* **Products of sound keys are sound** (`prodKeys_sound`), and two product keys are apart when
  either component is. A type and a channel name together give finer apartness than either alone.
* Apartness of distinct classes is sound by construction, so static independence read from class
  keys needs no widening.

## Controls: what breaks without invariance

`Controls` declares a theory that identifies the symbol `g` with `f` (an alias: `E` is the kernel
of renaming `g` to `f`), with `f`, `g` of sort `A` and `c` of sort `B`.

* **Head keys are unsound for it** (`Controls.headKeys_unsound`): the value `g` solves the pattern
  `f` modulo the theory and has head `g`. Reading heads as channel names, an alias between two names
  breaks name keys: a receive on `f` matches a message on `g`.
* **The head keys' apartness is wrong for it** (`Controls.head_apartness_wrong`): head keys declare
  the patterns `f` and `g` apart, and one value solves both.
* **Sort keys are sound for it** (`Controls.sortKeys_sound`): the alias preserves sorts. They do not
  declare `f` and `g` apart (`Controls.sort_keys_not_apart_fg`), and they do declare `f` and `c`
  apart (`Controls.sort_keys_apart_fc`).
* A theory that relates values of different sorts makes sort keys unsound
  (`Controls.sortKeys_unsound_for_sort_changing`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uV uT uP uC uK

variable {V : Type uV} {T : Type uT} {P : Type uP}

/-! ## Classifications preserved by the theory -/

/-- **A classification of values preserved by the theory**, with patterns classified soundly: a
pattern with a class has only instances of that class. -/
structure Classing (L : TermLayer V T P) (C : Type uC) where
  classOf : T → C
  invariant : ∀ u t, L.E u t → classOf u = classOf t
  patClass : P → Option C
  inst_sound : ∀ σ p u c, patClass p = some c → L.inst σ p = some u → classOf u = c

variable {L : TermLayer V T P} {C : Type uC}

/-- What a class key covers: `some c` covers the values of class `c`, `none` covers everything. -/
def classCovers (cl : Classing L C) : Option C → T → Prop
  | none, _ => True
  | some c, t => cl.classOf t = c

/-- Two class keys are apart when both are classes and they differ. -/
def classApart [DecidableEq C] : Option C → Option C → Bool
  | some c, some c' => decide (c ≠ c')
  | _, _ => false

/-- **The keys of a classification.** -/
def classKeys [DecidableEq C] (cl : Classing L C) : RegionKeys T P (Option C) where
  covers := classCovers cl
  keys p := [cl.patClass p]
  apart := classApart
  apart_sound := by
    intro k k' apart t covers covers'
    cases k with
    | none => simp [classApart] at apart
    | some c =>
        cases k' with
        | none => simp [classApart] at apart
        | some c' =>
            simp only [classApart, decide_eq_true_eq] at apart
            exact apart (covers.symm.trans covers')

/-- **Class keys are sound modulo the theory.** -/
theorem classKeys_sound [DecidableEq C] (cl : Classing L C) : (classKeys cl).Sound L := by
  intro σ p t solves
  obtain ⟨u, inst, equal⟩ := solves
  refine ⟨cl.patClass p, List.mem_singleton_self _, ?_⟩
  cases classed : cl.patClass p with
  | none => trivial
  | some c =>
      show cl.classOf t = c
      rw [← cl.invariant u t equal]
      exact cl.inst_sound σ p u c classed inst

/-! ## Products of keys -/

variable {K₁ : Type uK} {K₂ : Type uK}

/-- **The product of two key systems**: a pair covers what both cover, and is apart from another
when either component is. -/
def prodKeys (R₁ : RegionKeys T P K₁) (R₂ : RegionKeys T P K₂) : RegionKeys T P (K₁ × K₂) where
  covers k t := R₁.covers k.1 t ∧ R₂.covers k.2 t
  keys p := (R₁.keys p).flatMap fun k₁ => (R₂.keys p).map fun k₂ => (k₁, k₂)
  apart k k' := R₁.apart k.1 k'.1 || R₂.apart k.2 k'.2
  apart_sound := by
    intro k k' apart t covers covers'
    rcases Bool.or_eq_true _ _ |>.mp apart with first | second
    · exact R₁.apart_sound _ _ first t covers.1 covers'.1
    · exact R₂.apart_sound _ _ second t covers.2 covers'.2

/-- **Products of sound keys are sound.** -/
theorem prodKeys_sound {R₁ : RegionKeys T P K₁} {R₂ : RegionKeys T P K₂} (sound₁ : R₁.Sound L)
    (sound₂ : R₂.Sound L) : (prodKeys R₁ R₂).Sound L := by
  intro σ p t solves
  obtain ⟨k₁, in₁, covers₁⟩ := sound₁ σ p t solves
  obtain ⟨k₂, in₂, covers₂⟩ := sound₂ σ p t solves
  refine ⟨(k₁, k₂), ?_, covers₁, covers₂⟩
  exact List.mem_flatMap.mpr ⟨k₁, in₁, List.mem_map.mpr ⟨k₂, in₂, rfl⟩⟩

/-! ## The kernel of a renaming of symbols, as a theory -/

namespace Renaming

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative

variable {F : Type} [DecidableEq F] {W : Type} [DecidableEq W]

/-- Rename every symbol of a value. -/
def rename (φ : F → F) : Tm F → Tm F
  | .leaf a => .leaf (φ a)
  | .node f l r => .node (φ f) (rename φ l) (rename φ r)

omit [DecidableEq F] in
theorem inst_congr (φ : F → F) (σ τ : Subst W (Tm F)) :
    ∀ p : Pat W F, (∀ v ∈ p.vars, Option.Rel (fun s t => rename φ s = rename φ t) (σ v) (τ v)) →
      Option.Rel (fun s t => rename φ s = rename φ t) (p.inst σ) (p.inst τ)
  | .var v, same => same v (by simp [Pat.vars])
  | .leaf a, _ => Option.Rel.some rfl
  | .node f p q, same => by
      have relP := inst_congr φ σ τ p fun v h => same v (by simp [Pat.vars, h])
      have relQ := inst_congr φ σ τ q fun v h => same v (by simp [Pat.vars, h])
      simp only [Pat.inst]
      rcases optionRel_iff.mp relP with ⟨hp, hp'⟩ | ⟨l, l', hp, hp', rl⟩ <;>
        rcases optionRel_iff.mp relQ with ⟨hq, hq'⟩ | ⟨r, r', hq, hq', rr⟩ <;>
        simp only [hp, hp', hq, hq'] <;> try exact Option.Rel.none
      exact Option.Rel.some (by simp only [rename, rl, rr])

/-- **The theory identifying values with one renaming**: `s =_E t` when renaming makes them equal. -/
def layer (φ : F → F) : TermLayer W (Tm F) (Pat W F) where
  E s t := rename φ s = rename φ t
  equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
  vars := Pat.vars
  inst σ p := p.inst σ
  inst_bound σ p := (Pat.inst_isSome σ p).mp
  inst_local σ τ p := Pat.inst_local σ τ p
  inst_congr σ τ p := inst_congr φ σ τ p

omit [DecidableEq F] [DecidableEq W] in
theorem head_rename (φ : F → F) : ∀ t : Tm F, (rename φ t).head = φ t.head
  | .leaf _ => rfl
  | .node _ _ _ => rfl

/-- **Sorts of head symbols form a classification** of the renaming theory when the renaming
preserves sorts. -/
def sortClassing {S : Type} (φ : F → F) (sortOf : F → S) (preserves : ∀ f, sortOf (φ f) = sortOf f) :
    Classing (layer (W := W) φ) S where
  classOf t := sortOf t.head
  invariant u t equal := by
    have heads : (rename φ u).head = (rename φ t).head := congrArg Tm.head equal
    rw [head_rename, head_rename] at heads
    have sorted := congrArg sortOf heads
    rwa [preserves, preserves] at sorted
  patClass p := p.head?.map sortOf
  inst_sound σ p u c classed inst := by
    cases headed : p.head? with
    | none => simp [headed] at classed
    | some g =>
        rw [headed] at classed
        simp only [Option.map_some, Option.some.injEq] at classed
        rw [← classed, Pat.head_inst headed inst]

end Renaming

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative
open Renaming

/-- Three symbols: `f` and `g` of sort `A`, `c` of sort `B`. -/
inductive Sym where
  | f | g | c
  deriving DecidableEq, Repr

/-- Two sorts. -/
inductive Sort' where
  | A | B
  deriving DecidableEq, Repr

/-- The sort of a symbol. -/
def sortOf : Sym → Sort'
  | .f => .A
  | .g => .A
  | .c => .B

/-- The alias: `g` is renamed to `f`. -/
def aliasG : Sym → Sym
  | .g => .f
  | s => s

/-- A renaming that relates `c`, of sort `B`, to `f`, of sort `A`. -/
def sortChanging : Sym → Sym
  | .c => .f
  | s => s

/-- The theory of the alias. -/
abbrev La : TermLayer ℕ (Tm Sym) (Pat ℕ Sym) := layer aliasG

/-- The sort classification of the alias theory. -/
def sorts : Classing La Sort' := sortClassing aliasG sortOf (by intro s; cases s <;> rfl)

/-- Head keys for the alias theory. -/
abbrev heads : RegionKeys (Tm Sym) (Pat ℕ Sym) (Key Sym) := regionKeys headKeys

/-- A constant solves a constant modulo the alias when the alias identifies them. -/
theorem solves_leaf (a b : Sym) (same : aliasG a = aliasG b) :
    La.Solves (fun _ => none) (.leaf a) (.leaf b) := by
  refine ⟨.leaf a, rfl, ?_⟩
  show rename aliasG (.leaf a) = rename aliasG (.leaf b)
  simp only [rename, same]

/-- **Head keys are unsound for the alias**: `g` solves the pattern `f` and is not covered. -/
theorem headKeys_unsound : ¬ heads.Sound La := by
  intro sound
  obtain ⟨k, member, covers⟩ :=
    sound (fun _ => none) (.leaf .f) (.leaf .g) ⟨.leaf .f, rfl, rfl⟩
  simp only [heads, regionKeys, headKeys, List.mem_singleton] at member
  subst member
  have wrongHead : (Tm.leaf Sym.g).head = Sym.f := covers
  exact absurd wrongHead (by decide)

/-- **The head keys' apartness is wrong for the alias**: they declare `f` and `g` apart, and the
value `g` solves both modulo the theory. -/
theorem head_apartness_wrong :
    heads.AllApart (heads.keys (.leaf .f)) (heads.keys (.leaf .g)) ∧
      La.Solves (fun _ => none) (.leaf .f) (.leaf .g) ∧ La.Solves (fun _ => none) (.leaf .g) (.leaf .g) :=
  ⟨by decide, solves_leaf .f .g rfl, solves_leaf .g .g rfl⟩

/-- **Sort keys are sound for the alias.** -/
theorem sortKeys_sound : (classKeys sorts).Sound La := classKeys_sound sorts

/-- Sort keys do not declare `f` and `g` apart. -/
theorem sort_keys_not_apart_fg :
    ¬ (classKeys sorts).AllApart ((classKeys sorts).keys (.leaf .f)) ((classKeys sorts).keys (.leaf .g)) := by
  intro apart
  have := apart _ List.mem_cons_self _ List.mem_cons_self
  simp [classKeys, classApart, sorts, sortClassing, sortOf, Pat.head?] at this

/-- Sort keys declare `f` and `c` apart, soundly. -/
theorem sort_keys_apart_fc :
    (classKeys sorts).AllApart ((classKeys sorts).keys (.leaf .f)) ((classKeys sorts).keys (.leaf .c)) := by
  intro k member k' member'
  simp only [classKeys, List.mem_singleton] at member member'
  subst member member'
  simp [classKeys, classApart, sorts, sortClassing, sortOf, Pat.head?]

/-- The theory relating `c` to `f`. -/
abbrev Lx : TermLayer ℕ (Tm Sym) (Pat ℕ Sym) := layer sortChanging

/-- **A theory that relates values of different sorts makes sort keys unsound**: the sort key of
the pattern `c` is `B`, and `f`, of sort `A`, solves it. -/
theorem sortKeys_unsound_for_sort_changing :
    Lx.Solves (fun _ => none) (.leaf .c) (.leaf .f) ∧ sortOf (Tm.head (.leaf .f : Tm Sym)) ≠ sortOf .c :=
  ⟨⟨.leaf .c, rfl, by show rename sortChanging (.leaf .c) = rename sortChanging (.leaf .f); rfl⟩,
    by decide⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
