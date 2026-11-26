import Mettapedia.GSLT.Contracts.ScopedTheoryImports

/-! Profiles have two different composition laws. A local policy may replace
an inherited policy; ordered rule occurrences accumulate. A client discovers
which of either kind it uses by reading the composed theory. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.Contracts.DialectProfileComposition

open Mettapedia.Machines.ReadOnlyQuery
open ScopedTheoryImports (Environment shadow)

variable {S K B R A : Type*}

structure Layer (S K B R : Type*) where
  policies : Environment S B
  catalogues : K → List R

def empty : Layer S K B R := ⟨fun _ => none, fun _ => []⟩

def overlay (parent child : Layer S K B R) : Layer S K B R :=
  ⟨shadow parent.policies child.policies, fun k => parent.catalogues k ++ child.catalogues k⟩

theorem overlay_assoc (a b c : Layer S K B R) :
    overlay (overlay a b) c = overlay a (overlay b c) := by
  simp only [overlay, ScopedTheoryImports.shadow_assoc, List.append_assoc]

theorem empty_left (p : Layer S K B R) : overlay empty p = p := by
  have eq : shadow (fun _ => none) p.policies = p.policies := by
    funext s; cases h : p.policies s <;> simp [shadow, h]
  simp [empty, overlay, eq]

theorem empty_right (p : Layer S K B R) : overlay p empty = p := by
  have eq : shadow p.policies (fun _ => none) = p.policies := rfl
  simp [empty, overlay, eq]

abbrev Port (S K : Type*) := Sum S K
abbrev Reply (B R : Type*) := Sum (Option B) (List R)

def read (p : Layer S K B R) : Port S K → Reply B R
  | .inl s => .inl (p.policies s)
  | .inr k => .inr (p.catalogues k)

/-- An absent override and a redundant override are both harmless to this
lookup. Even one new duplicate changes the ordered catalogue read. -/
def Harmless (p delta : Layer S K B R) : Port S K → Prop
  | .inl s => delta.policies s = none ∨ delta.policies s = p.policies s
  | .inr k => delta.catalogues k = []

theorem same_read_iff (p delta : Layer S K B R) (port : Port S K) :
    read (overlay p delta) port = read p port ↔ Harmless p delta port := by
  cases port with
  | inl s =>
    cases hd : delta.policies s <;> simp [read, overlay, shadow, Harmless, hd]
  | inr k => simp [read, overlay, Harmless]

/-- Necessary and sufficient for replay of this *trace*. Two different
traces can of course still give the same terminal answer. No static list
of language-wide policy dependencies is assumed. -/
theorem overlay_replay_iff (p delta : Layer S K B R) (q : Program (Port S K) (Reply B R) A) :
    run (read (overlay p delta)) q = run (read p) q ↔
      ∀ event ∈ (run (read p) q).reads, Harmless p delta event.1 := by
  constructor
  · intro eq event hr
    apply (same_read_iff p delta _).mp
    have newer := run_agrees (read (overlay p delta)) q
    rw [eq] at newer
    exact (newer event hr).trans (run_agrees (read p) q event hr).symm
  · intro good
    apply run_eq_of_agrees
    intro event hr
    exact ((same_read_iff p delta _).mpr (good event hr)).trans (run_agrees (read p) q event hr)

/-- Transport a result across different profiles by the reads made by
*both* the reference and its realization. They need not make the same
reads, produce the same representation, or agree on unobserved output. -/
theorem transport_region {V W O : Type*} (p₁ p₂ : Layer S K B R)
    (spec : Program (Port S K) (Reply B R) V) (plan : Program (Port S K) (Reply B R) W)
    (observe : V → O) (emit : W → O)
    (before : emit (run (read p₁) plan).answer = observe (run (read p₁) spec).answer)
    (agreement : ∀ event ∈ (run (read p₁) plan).reads ++ (run (read p₁) spec).reads,
      read p₂ event.1 = event.2) :
    emit (run (read p₂) plan).answer = observe (run (read p₂) spec).answer := by
  obtain ⟨hp, hs⟩ := (agrees_append _ _ _).mp agreement
  rwa [run_eq_of_agrees _ _ plan hp, run_eq_of_agrees _ _ spec hs]

private def off : Layer Unit Unit Bool Bool := empty
private def on : Layer Unit Unit Bool Bool := ⟨fun _ => some true, fun _ => []⟩
private def consult : Program (Port Unit Unit) (Reply Bool Bool) Bool :=
  .read (.inl ()) fun answer => .pure (answer == .inl (some true))

/-- Watching only the optimized route is not enough: a constant plan
remains unchanged as the source's previously absent policy becomes active. -/
theorem plan_alone_is_insufficient :
    let plan : Program (Port Unit Unit) (Reply Bool Bool) Bool := .pure false
    (run (read off) plan).answer = (run (read off) consult).answer ∧
    (run (read on) plan).reads = (run (read off) plan).reads ∧
    (run (read on) plan).answer ≠ (run (read on) consult).answer := by decide

end Mettapedia.GSLT.Contracts.DialectProfileComposition
