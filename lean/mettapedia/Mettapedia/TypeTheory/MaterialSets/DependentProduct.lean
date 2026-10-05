import Mettapedia.TypeTheory.MaterialSets.DependentSum

/-!
# Material dependent products from function graphs

The dependent product is a separated subset of the powerset of the dependent-pair
set. Its members are total, single-valued graphs; the powerset bound excludes
extraneous graph entries. Evaluation takes the union of the image of the second
projection of a graph row. This recovers the unique value without choosing a
witness from an existential.

The comparison with dependent functions assumes extensional sets,
propositional membership, and recovery of membership evidence. All set operations
are supplied explicitly. No form of choice, foundation, or universal set is
assumed. This result concerns extensional material membership, not proof-relevant
edge occurrences of a graph presentation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets

universe u v

variable {S : Type u} (Mem : S → S → Sort v)

/-- Separation, characterized by its membership law. -/
structure SeparationOperation where
  sep : (S → Prop) → S → S
  nonempty_mem_sep_iff : ∀ {x X : S} {p : S → Prop},
    Nonempty (Mem x (sep p X)) ↔ Nonempty (Mem x X) ∧ p x

/-- Powerset, characterized by inclusion of members. -/
structure PowersetOperation where
  powerset : S → S
  nonempty_mem_powerset_iff : ∀ {Y X : S},
    Nonempty (Mem Y (powerset X)) ↔
      ∀ z, Nonempty (Mem z Y) → Nonempty (Mem z X)

variable {Mem}
variable (R : DependentReplacement Mem) (U : UnionOperation Mem) (P : Pairing S)
variable (A : SeparationOperation Mem) (Q : PowersetOperation Mem)

/-- The graph of an actual dependent function. -/
def functionGraph {X : S} {B : El Mem X → S} (f : ∀ a, El Mem (B a)) : S :=
  R.image X fun a => P.pair a.1 (f a).1

/-- Each argument has a graph entry, and every entry over it has the same value.
The graph's inclusion in the dependent-pair set is imposed separately. -/
def IsFunctionGraph (X : S) (B : El Mem X → S) (G : S) : Prop :=
  ∀ a : El Mem X, ∃ b : El Mem (B a),
    Nonempty (Mem (P.pair a.1 b.1) G) ∧
      ∀ z, Nonempty (Mem z G) → P.fst z = a.1 → P.snd z = b.1

/-- Total single-valued subsets of the set of dependent pairs. -/
def piSet (X : S) (B : El Mem X → S) : S :=
  A.sep (IsFunctionGraph P X B) (Q.powerset (sigmaSet R U P X B))

theorem nonempty_mem_piSet_iff {X G : S} {B : El Mem X → S} :
    Nonempty (Mem G (piSet R U P A Q X B)) ↔
      (∀ z, Nonempty (Mem z G) → Nonempty (Mem z (sigmaSet R U P X B))) ∧
        IsFunctionGraph P X B G := by
  rw [piSet, A.nonempty_mem_sep_iff, Q.nonempty_mem_powerset_iff]

theorem functionGraph_bound {X : S} {B : El Mem X → S} (f : ∀ a, El Mem (B a)) :
    ∀ z, Nonempty (Mem z (functionGraph R P f)) →
      Nonempty (Mem z (sigmaSet R U P X B)) := by
  rintro z ⟨hz⟩
  obtain ⟨a, rfl⟩ := R.exists_of_mem_image hz
  exact ⟨(pairMember R U P ⟨a, f a⟩).2⟩

theorem functionGraph_isFunctionGraph (h : PropositionalMembership Mem) {X : S}
    {B : El Mem X → S} (f : ∀ a, El Mem (B a)) :
    IsFunctionGraph P X B (functionGraph R P f) := by
  intro a
  refine ⟨f a, ⟨R.mem_image (fun a => P.pair a.1 (f a).1) a⟩, ?_⟩
  rintro z ⟨hz⟩ first
  obtain ⟨a', rfl⟩ := R.exists_of_mem_image hz
  rw [P.fst_pair] at first
  obtain rfl : a' = a := El.ext h first
  exact P.snd_pair _ _

/-- Encode a dependent function as a member of its material dependent product. -/
def graphMember (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem)
    {X : S} {B : El Mem X → S} (f : ∀ a, El Mem (B a)) :
    El Mem (piSet R U P A Q X B) :=
  ⟨functionGraph R P f, r.recover (nonempty_mem_piSet_iff R U P A Q |>.mpr
    ⟨functionGraph_bound R U P f, functionGraph_isFunctionGraph R P h f⟩)⟩

/-- The material set collecting the values in one graph row. -/
def graphRow (G x : S) : S :=
  R.image (A.sep (fun z => P.fst z = x) G) fun z => P.snd z.1

/-- Union recovers the value of a singleton graph row. -/
def graphValue (G x : S) : S :=
  U.union (graphRow R P A G x)

theorem graphValue_eq_of_witness (r : EvidenceRecovery Mem) (hext : Extensional Mem)
    {X G : S} {B : El Mem X → S} (a : El Mem X) (b : El Mem (B a))
    (entry : Nonempty (Mem (P.pair a.1 b.1) G))
    (unique : ∀ z, Nonempty (Mem z G) → P.fst z = a.1 → P.snd z = b.1) :
    graphValue R U P A G a.1 = b.1 := by
  apply hext
  intro y
  constructor
  · rintro ⟨hy⟩
    obtain ⟨W, ⟨hyW⟩, ⟨hW⟩⟩ := U.exists_of_mem_union hy
    obtain ⟨z, rfl⟩ := R.exists_of_mem_image hW
    obtain ⟨hz, first⟩ := A.nonempty_mem_sep_iff.mp ⟨z.2⟩
    exact ⟨unique z.1 hz first ▸ hyW⟩
  · rintro ⟨hy⟩
    let z : El Mem (A.sep (fun z => P.fst z = a.1) G) :=
      ⟨P.pair a.1 b.1, r.recover (A.nonempty_mem_sep_iff.mpr
        ⟨entry, P.fst_pair _ _⟩)⟩
    have hrow : Mem b.1 (graphRow R P A G a.1) := by
      have hz := R.mem_image (fun z => P.snd z.1) z
      change Mem (P.snd (P.pair a.1 b.1)) (graphRow R P A G a.1) at hz
      rw [P.snd_pair] at hz
      exact hz
    exact ⟨U.mem_union hy hrow⟩

theorem nonempty_mem_graphValue (r : EvidenceRecovery Mem) (hext : Extensional Mem)
    {X G : S} {B : El Mem X → S} (good : IsFunctionGraph P X B G) (a : El Mem X) :
    Nonempty (Mem (graphValue R U P A G a.1) (B a)) := by
  obtain ⟨b, entry, unique⟩ := good a
  rw [graphValue_eq_of_witness R U P A r hext a b entry unique]
  exact ⟨b.2⟩

/-- Evaluate a material function graph, retaining its fibre membership evidence. -/
def evalGraph (r : EvidenceRecovery Mem) (hext : Extensional Mem)
    {X : S} {B : El Mem X → S} (g : El Mem (piSet R U P A Q X B))
    (a : El Mem X) : El Mem (B a) :=
  ⟨graphValue R U P A g.1 a.1, r.recover (nonempty_mem_graphValue R U P A r hext
    (nonempty_mem_piSet_iff R U P A Q |>.mp ⟨g.2⟩).2 a)⟩

theorem evalGraph_fst_eq_of_entry (r : EvidenceRecovery Mem) (hext : Extensional Mem)
    {X : S} {B : El Mem X → S} (g : El Mem (piSet R U P A Q X B))
    (a : El Mem X) (b : El Mem (B a))
    (entry : Nonempty (Mem (P.pair a.1 b.1) g.1)) :
    (evalGraph R U P A Q r hext g a).1 = b.1 := by
  obtain ⟨b₀, entry₀, unique⟩ := (nonempty_mem_piSet_iff R U P A Q |>.mp ⟨g.2⟩).2 a
  exact (graphValue_eq_of_witness R U P A r hext a b₀ entry₀ unique).trans
    ((P.snd_pair _ _).symm.trans (unique _ entry (P.fst_pair _ _))).symm

/-- Evaluation of a graph built from a dependent function returns that function. -/
theorem evalGraph_beta (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem)
    (hext : Extensional Mem) {X : S} {B : El Mem X → S} (f : ∀ a, El Mem (B a))
    (a : El Mem X) :
    evalGraph R U P A Q r hext (graphMember R U P A Q h r f) a = f a := by
  apply El.ext h
  exact evalGraph_fst_eq_of_entry R U P A Q r hext _ a (f a)
    ⟨R.mem_image (fun a => P.pair a.1 (f a).1) a⟩

/-- Re-encoding evaluation recovers the whole graph. The powerset bound is
essential here: every original graph entry is a valid dependent pair. -/
theorem functionGraph_evalGraph (r : EvidenceRecovery Mem) (hext : Extensional Mem)
    {X : S} {B : El Mem X → S} (g : El Mem (piSet R U P A Q X B)) :
    functionGraph R P (evalGraph R U P A Q r hext g) = g.1 := by
  obtain ⟨bound, good⟩ := nonempty_mem_piSet_iff R U P A Q |>.mp ⟨g.2⟩
  apply hext
  intro z
  constructor
  · rintro ⟨hz⟩
    obtain ⟨a, rfl⟩ := R.exists_of_mem_image hz
    obtain ⟨b, entry, unique⟩ := good a
    have value := graphValue_eq_of_witness R U P A r hext a b entry unique
    change Nonempty (Mem (P.pair a.1 (graphValue R U P A g.1 a.1)) g.1)
    rw [value]
    exact entry
  · intro hz
    obtain ⟨ms⟩ := bound z hz
    obtain ⟨a, b, rfl⟩ := exists_of_mem_sigmaSet R U P ms
    have value := evalGraph_fst_eq_of_entry R U P A Q r hext g a b hz
    exact ⟨value ▸ R.mem_image (fun a => P.pair a.1
      (evalGraph R U P A Q r hext g a).1) a⟩

/-- Members of the material dependent product are actual dependent functions.
Evaluation is constructed from the set operations, without existential choice. -/
def piSetEquiv (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem)
    (hext : Extensional Mem) (X : S) (B : El Mem X → S) :
    El Mem (piSet R U P A Q X B) ≃ (∀ a, El Mem (B a)) where
  toFun := evalGraph R U P A Q r hext
  invFun := graphMember R U P A Q h r
  left_inv g := El.ext h (functionGraph_evalGraph R U P A Q r hext g)
  right_inv f := funext (evalGraph_beta R U P A Q h r hext f)

/-- The product is inhabited exactly when an actual dependent section exists.
This does not infer a section merely from propositional nonemptiness of every
fibre; that inference would require a separate choice principle. -/
theorem nonempty_el_piSet_iff (h : PropositionalMembership Mem)
    (r : EvidenceRecovery Mem) (hext : Extensional Mem) (X : S) (B : El Mem X → S) :
    Nonempty (El Mem (piSet R U P A Q X B)) ↔ Nonempty (∀ a, El Mem (B a)) :=
  ⟨fun ⟨g⟩ => ⟨piSetEquiv R U P A Q h r hext X B g⟩,
    fun ⟨f⟩ => ⟨(piSetEquiv R U P A Q h r hext X B).symm f⟩⟩

/-- Extensional material graphs faithfully encode dependent functions when
membership evidence is propositional. -/
theorem functionGraph_injective (h : PropositionalMembership Mem)
    {X : S} {B : El Mem X → S} :
    Function.Injective (functionGraph R P : (∀ a, El Mem (B a)) → S) := by
  intro f g same
  funext a
  apply El.ext h
  have entry : Mem (P.pair a.1 (f a).1) (functionGraph R P g) :=
    same ▸ R.mem_image (fun a => P.pair a.1 (f a).1) a
  obtain ⟨a', e⟩ := R.exists_of_mem_image entry
  have first := congrArg P.fst e
  rw [P.fst_pair, P.fst_pair] at first
  obtain rfl : a' = a := El.ext h first
  exact ((P.snd_pair _ _).symm.trans ((congrArg P.snd e).trans (P.snd_pair _ _))).symm

/-- An empty domain has exactly one material function graph, even if its fibres
are empty. -/
theorem piSet_subsingleton_of_empty_domain (h : PropositionalMembership Mem)
    (r : EvidenceRecovery Mem) (hext : Extensional Mem) {X : S} {B : El Mem X → S}
    (empty : ∀ _ : El Mem X, False) : Subsingleton (El Mem (piSet R U P A Q X B)) := by
  refine ⟨fun g g' => (piSetEquiv R U P A Q h r hext X B).injective ?_⟩
  exact funext fun a => (empty a).elim

theorem nonempty_piSet_of_empty_domain (h : PropositionalMembership Mem)
    (r : EvidenceRecovery Mem) {X : S} {B : El Mem X → S}
    (empty : ∀ _ : El Mem X, False) : Nonempty (El Mem (piSet R U P A Q X B)) :=
  ⟨graphMember R U P A Q h r fun a => (empty a).elim⟩

/-- A domain member with an empty fibre prevents every material function graph. -/
theorem not_nonempty_piSet_of_empty_fibre (r : EvidenceRecovery Mem)
    (hext : Extensional Mem) {X : S} {B : El Mem X → S} (a : El Mem X)
    (empty : ∀ _ : El Mem (B a), False) :
    ¬ Nonempty (El Mem (piSet R U P A Q X B)) := by
  rintro ⟨g⟩
  exact empty (evalGraph R U P A Q r hext g a)

end Mettapedia.TypeTheory.MaterialSets
