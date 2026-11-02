import Mettapedia.Machines.ShapeScopedUnification
import Mettapedia.Machines.NamedStoreHolders

/-!
# A composed oracle for recursive named shape stores

Starting from a codec resolver and its naming operation, construct recursive
shape bodies that only quote proper subterms. The resulting graph has a
derived decreasing rank and unfolds to the original codec value. This proves
more than a conditional graph interface: the shape construction actually
satisfies it. Re-cutting changes the bodies without changing any decoded name.

The source resolver is an abstract read interface. This construction is a
reference representation, not an allocation algorithm, global interning
implementation, authority policy, or verification of native accessors.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NamedStoreModel

open ShapeStore NamedShapeGraph

variable {α Name : Type}

def bodies (read : Name → Option (Tm α)) (name : Tm α → Name)
    (policy : Policy α) : Heap α Name :=
  fun n => (read n).map (quoteBody name policy)

def rank (read : Name → Option (Tm α)) (n : Name) : Nat :=
  ((read n).map termSize).getD 0

theorem bodies_ranked (read : Name → Option (Tm α)) (name : Tm α → Name)
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α) :
    Ranked (bodies read name policy) (rank read) := by
  intro n e found child occurs
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨sub, equal, smaller⟩ := quoteBody_refs_strict name policy t child occurs
  subst child
  constructor
  · simpa [rank, roundtrip, ht] using smaller
  · exact ⟨quoteBody name policy sub, by simp [bodies, roundtrip]⟩

theorem bodies_sound (read : Name → Option (Tm α)) (name : Tm α → Name)
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α)
    (depth : Nat) (n : Name) (t : Tm α)
    (expanded : unfoldName (bodies read name policy) depth n = some t) : read n = some t := by
  induction depth generalizing n t with
  | zero => simp [unfoldName] at expanded
  | succ depth ih =>
      obtain ⟨e, found, he⟩ := Option.bind_eq_some_iff.mp expanded
      obtain ⟨original, horiginal, rfl⟩ := Option.map_eq_some_iff.mp found
      have result := eval_extension (quoteBody name policy original) _ read
        (fun n t accepted => ih n t accepted) t he
      rw [quoteBody_eval name read roundtrip policy original] at result
      exact horiginal.trans result

/-- The reference-depth bound is computed from the original finite term.
It is not a bound on physical expansion size or machine instructions. -/
theorem bodies_complete (read : Name → Option (Tm α)) (name : Tm α → Name)
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α)
    (n : Name) (t : Tm α) (found : read n = some t) :
    unfoldName (bodies read name policy) (termSize t + 1) n = some t := by
  have bodyFound : bodies read name policy n = some (quoteBody name policy t) := by
    simp [bodies, found]
  obtain ⟨expanded, success⟩ := ranked_unfolds _ (rank read)
    (bodies_ranked read name roundtrip policy) n _ bodyFound
  have original := bodies_sound read name roundtrip policy _ n expanded success
  have equal : expanded = t := Option.some.inj (original.symm.trans found)
  subst expanded
  simpa [rank, found] using success

/-- All policies retain the same logical names, with no global home change. -/
theorem recut_preserves_name (read : Name → Option (Tm α)) (name : Tm α → Name)
    (roundtrip : ∀ t, read (name t) = some t) (first second : Policy α)
    (n : Name) (t : Tm α) (found : read n = some t) :
    unfoldName (bodies read name first) (termSize t + 1) n =
      unfoldName (bodies read name second) (termSize t + 1) n := by
  rw [bodies_complete read name roundtrip first n t found,
    bodies_complete read name roundtrip second n t found]

/-- Instantiate the recursive construction with the disjoint family of
codecs and its chosen canonical home. -/
theorem codec_family_unfolds {Store : Type} {Code : Store → Type}
    (family : ∀ s, NamesOverStores.Codec (Tm α) (Code s))
    (home : Tm α → Store) (policy : Policy α) (t : Tm α) :
    unfoldName (bodies (NamesOverStores.decode family) (NamesOverStores.name family home) policy)
      (termSize t + 1) (NamesOverStores.name family home t) = some t := by
  exact bodies_complete _ _ (NamesOverStores.decode_name family home) policy _ t
    (NamesOverStores.decode_name family home t)

/-- Per-skeleton admission, rather than universal codec coverage, suffices. -/
theorem admitted_family_unfolds {Store : Type} {Code : Store → Type}
    (naming : NamesOverStores.AdmittedNaming (Tm α) Code) (policy : Policy α) (t : Tm α) :
    unfoldName (bodies naming.read naming.name policy) (termSize t + 1) (naming.name t) = some t :=
  bodies_complete naming.read naming.name naming.read_name policy _ t (naming.read_name t)

/-- Exact expansion connects the shape compiler to scoped first-order
unification. Availability is required only for this row's actual holes. -/
theorem scoped_reader_oracle {Var : Type}
    (read : Name → Option (ShapeScopedUnification.OpenTerm α Var))
    (values : Name → ShapeScopedUnification.OpenTerm α Var)
    (e : ShapeScopedUnification.View α Var Name)
    (available : ∀ n ∈ e.refs, read n = some (values n))
    (t p : ShapeScopedUnification.OpenTerm α Var) (expanded : e.eval read = some t)
    (queryScope rowScope : Nat)
    (θ : Mettapedia.Logic.LP.Subst (ShapeScopedUnification.signature α Var)) :
    Mettapedia.Logic.LP.Unifies θ
      (ShapeScopedUnification.constraints values queryScope rowScope p e) ↔
    θ.applyTerm (ShapeScopedUnification.encode queryScope p) =
      θ.applyTerm (ShapeScopedUnification.encode rowScope t) := by
  have equal : e.plug values = t :=
    Option.some.inj ((eval_plug e read values available).symm.trans expanded)
  rw [ShapeScopedUnification.constraints_exact, equal]

/-- The holder census reads all outgoing slots, including repeated names. -/
def references (heap : Heap α Name) (n : Name) : List Name :=
  match heap n with
  | none => []
  | some e => e.refs

/-- The concrete recursive shape construction earns the collector's
acyclicity condition. The finite allocation inventory and roots must still
be complete and reference-closed. -/
theorem constructed_collection_exact [DecidableEq Name]
    (read : Name → Option (Tm α)) (name : Tm α → Name)
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α)
    (roots : List Name) (allocated : Finset Name)
    (closed : NamedStoreHolders.Closed roots (references (bodies read name policy)) allocated)
    (n : Name) :
    n ∈ NamedStoreHolders.sweep roots (references (bodies read name policy)) allocated.card allocated ↔
      Mettapedia.GSLT.Dynamics.StoreReachability.Reach
        (NamedStoreHolders.graph roots (references (bodies read name policy)) allocated) n := by
  apply NamedStoreHolders.sweep_exact roots _ allocated closed (rank read)
    (allocated.sup (rank read))
  · intro x hx
    exact Finset.le_sup hx
  · intro parent _ child occurs
    cases found : bodies read name policy parent with
    | none => simp [references, found] at occurs
    | some body =>
        exact (bodies_ranked read name roundtrip policy parent body found child
          (by simpa [references, found] using occurs)).1

namespace Controls

abbrev N := NamesOverStores.Address (fun _ : Bool => Tm String)
def family (_ : Bool) : NamesOverStores.Codec (Tm String) (Tm String) :=
  NamesOverStores.recordCodec (Tm String)
def home : Tm String → Bool
  | .atom _ => false
  | .node _ _ => true
def exampleTerm : Tm String := .node (.atom "a") (.node (.atom "a") (.atom "b"))

/-- One store supplies leaves while another supplies constructor bodies. -/
example :
    unfoldName (bodies (NamesOverStores.decode family) (NamesOverStores.name family home)
      (fun _ _ => true)) 4 (NamesOverStores.name family home exampleTerm) = some exampleTerm := by
  decide

theorem no_cut_and_subterm_cut_agree :
    unfoldName (bodies (NamesOverStores.decode family) (NamesOverStores.name family home)
      (fun _ _ => false)) (termSize exampleTerm + 1) (NamesOverStores.name family home exampleTerm) =
    unfoldName (bodies (NamesOverStores.decode family) (NamesOverStores.name family home)
      (fun _ _ => true)) (termSize exampleTerm + 1) (NamesOverStores.name family home exampleTerm) :=
  recut_preserves_name _ _ (NamesOverStores.decode_name family home) _ _ _ _
    (NamesOverStores.decode_name family home exampleTerm)

end Controls

#print axioms bodies_ranked
#print axioms bodies_sound
#print axioms bodies_complete
#print axioms codec_family_unfolds
#print axioms scoped_reader_oracle

end Mettapedia.Machines.NamedStoreModel
