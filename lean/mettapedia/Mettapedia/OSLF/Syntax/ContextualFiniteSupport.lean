import Mettapedia.OSLF.Syntax.ContextualFamilyReindex
import Mettapedia.OSLF.Syntax.ContextualFamilySupport
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.NodupEquivFin

/-!
# Finite support frames for contextual declarations

An ambient contextual declaration family need not be finite. A duplicate-free
list of identities nevertheless determines a dense finite frame that preserves
each identity's contextual arity. Projection onto that frame followed by the
canonical restoration fixes every finite port.

A term can also be compiled directly into such a frame, without a fallback
image for unused names. Applying the resulting term to the associated slot
frame agrees with instantiating the original term.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily.FiniteSupport

variable {S : Signature} {V : Type} {source : V → MetaArity S}

abbrev declaration (names : List V) : Fin names.length → MetaArity S :=
  fun position => source names[position]

section Project

variable [DecidableEq V]

def index (names : List V) (name : V) (present : name ∈ names) : Fin names.length :=
  ⟨names.idxOf name, List.idxOf_lt_length_iff.mpr present⟩

theorem at_index (names : List V) (name : V) (present : name ∈ names) :
    names[index names name present] = name := List.getElem_idxOf _

def restore (names : List V) : Assignment (declaration (source := source) names) source :=
  reindex (fun position => names[position]) (fun _ => rfl)

def project (names : List V) (fallback : Assignment source (declaration (source := source) names)) :
    Assignment source (declaration (source := source) names) :=
  fun name => if present : name ∈ names then
    castMetaBody (congrArg source (at_index names name present))
      (generator (declaration (source := source) names) (index names name present))
  else fallback name

theorem project_outside (names : List V)
    (fallback : Assignment source (declaration (source := source) names))
    (name : V) (absent : name ∉ names) : project names fallback name = fallback name := by
  simp [project, absent]

theorem index_get (names : List V) (distinct : names.Nodup) (port : Fin names.length)
    (member : names[port] ∈ names) : index names names[port] member = port := by
  apply Fin.ext
  exact (distinct.getElem_inj_iff).mp (at_index names names[port] member)

theorem projection_at_port (names : List V) (distinct : names.Nodup)
    (fallback : Assignment source (declaration (source := source) names)) (port : Fin names.length) :
    project names fallback names[port] = generator (declaration (source := source) names) port := by
  have member : names[port] ∈ names := List.getElem_mem port.isLt
  rw [project, dif_pos member]
  exact cast_generator_of_identity (index_get names distinct port member) _

theorem project_restore (names : List V) (distinct : names.Nodup)
    (fallback : Assignment source (declaration (source := source) names)) :
    Assignment.compose (project names fallback) (restore names) =
      generator (declaration (source := source) names) := by
  funext port
  change instantiate (project names fallback)
      (reindex (fun position => names[position]) (fun _ => rfl) port) = _
  rw [instantiate_reindex]
  exact projection_at_port names distinct fallback port

end Project

section Compile

variable {W X : Type} {middle : W → MetaArity S} {target : X → MetaArity S}
  {allowed : V → Prop}

mutual

private def instantiateOn (image : (name : V) → allowed name →
    Term (signature S middle) (source name).1 (source name).2) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
      (∀ name ∈ support term, allowed name) → Term (signature S middle) Γ sort
  | _, _, .var position, _ => .var position
  | _, _, .op (.inl op) args, used => .op (.inl op) (instantiateArgsOn image args used)
  | _, _, .op (.inr (.mk name)) args, used =>
      bind (argsToSub (instantiateArgsOn image args
        (fun other present => used other (List.mem_cons_of_mem name present))))
        (image name (used name List.mem_cons_self))

private def instantiateArgsOn (image : (name : V) → allowed name →
    Term (signature S middle) (source name).1 (source name).2) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
      (args : Args (signature S source) arities Γ),
      (∀ name ∈ supportArgs args, allowed name) → Args (signature S middle) arities Γ
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, used =>
      .cons
        (instantiateOn image head (fun name present => used name (List.mem_append_left _ present)))
        (instantiateArgsOn image tail (fun name present => used name (List.mem_append_right _ present)))

end

mutual

private theorem instantiate_instantiateOn
    (image : (name : V) → allowed name → Term (signature S middle) (source name).1 (source name).2)
    (frame : Assignment middle target) (assignment : Assignment source target)
    (agree : ∀ name present, instantiate frame (image name present) = assignment name) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
      (used : ∀ name ∈ support term, allowed name),
      instantiate frame (instantiateOn image term used) = instantiate assignment term
  | _, _, .var _, _ => rfl
  | _, _, .op (.inl op) args, used => by
      simp only [instantiateOn, instantiate, instantiateArgs_instantiateArgsOn image frame assignment agree args used]
  | _, _, .op (.inr (.mk name)) args, used => by
      have arguments := instantiateArgs_instantiateArgsOn image frame assignment agree args
        (fun other present => used other (List.mem_cons_of_mem name present))
      simp only [instantiateOn, instantiate, instantiate_bind, agree, ← argsToSub_instantiateArgs, arguments]

private theorem instantiateArgs_instantiateArgsOn
    (image : (name : V) → allowed name → Term (signature S middle) (source name).1 (source name).2)
    (frame : Assignment middle target) (assignment : Assignment source target)
    (agree : ∀ name present, instantiate frame (image name present) = assignment name) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S} (args : Args (signature S source) arities Γ)
      (used : ∀ name ∈ supportArgs args, allowed name),
      instantiateArgs frame (instantiateArgsOn image args used) = instantiateArgs assignment args
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail, used => by
      simp only [instantiateArgsOn, instantiateArgs,
        instantiate_instantiateOn image frame assignment agree head,
        instantiateArgs_instantiateArgsOn image frame assignment agree tail]

end

variable [DecidableEq V]

/-- Retain distinct names in order of first use. -/
def firstNames (mentions : List V) : List V := mentions.reverse.dedup.reverse

theorem mem_firstNames {mentions : List V} {name : V} :
    name ∈ firstNames mentions ↔ name ∈ mentions := by
  simp [firstNames]

theorem firstNames_nodup (mentions : List V) : (firstNames mentions).Nodup :=
  List.nodup_reverse.mpr (List.nodup_dedup _)

theorem firstNames_map {Y : Type} [DecidableEq Y] (rename : V → Y)
    (injective : Function.Injective rename) (mentions : List V) :
    firstNames (mentions.map rename) = (firstNames mentions).map rename := by
  simp only [firstNames, ← List.map_reverse, List.dedup_map_of_injective injective]

/-- Any fixed slot code that can distinguish all the used identities must
provide at least as many positions as the first-use layout. -/
theorem firstNames_length_le (mentions : List V) {width : Nat} (encode : V → Fin width)
    (faithful : ∀ first ∈ mentions, ∀ second ∈ mentions, encode first = encode second → first = second) :
    (firstNames mentions).length ≤ width := by
  let names := firstNames mentions
  let code : Fin names.length → Fin width := fun slot => encode names[slot]
  have separate : Function.Injective code := by
    intro first second same
    apply Fin.ext
    apply ((firstNames_nodup mentions).getElem_inj_iff).mp
    exact faithful names[first] (mem_firstNames.mp (List.getElem_mem first.isLt))
      names[second] (mem_firstNames.mp (List.getElem_mem second.isLt)) same
  simpa [names] using Fintype.card_le_of_injective code separate

/-- The code uses dense declaration slots and the original object binders.
The support proof is erased and supplies no runtime fallback. -/
def compile (names : List V) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) (covered : ∀ name ∈ support term, name ∈ names) :
    Term (signature S (declaration (source := source) names)) Γ sort :=
  instantiateOn (fun name present =>
    castMetaBody (congrArg source (at_index names name present))
      (generator (declaration (source := source) names) (index names name present))) term covered

def slots (names : List V) (assignment : Assignment source target) :
    Assignment (declaration (source := source) names) target :=
  fun port => assignment names[port]

theorem instantiate_compile (names : List V) (assignment : Assignment source target)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
    (covered : ∀ name ∈ support term, name ∈ names) :
    instantiate (slots names assignment) (compile names term covered) = instantiate assignment term := by
  apply instantiate_instantiateOn
  intro name present
  rw [instantiate_castMetaBody, instantiate_generator]
  have castImage {first second : V} (same : first = second) :
      castMetaBody (V := signature S target) (congrArg source same) (assignment first) = assignment second := by
    cases same
    rfl
  exact castImage (at_index names name present)

end Compile

end Mettapedia.OSLF.Binding.ContextualFamily.FiniteSupport
