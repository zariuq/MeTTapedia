import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionCheck

/-! Reflection of successful source construction into the independently
declared admission conditions. This prevents admission from silently
narrowing the existing source-printer domain. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Datalog

theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β} {result : β}
    (accepted : value.bind next = .ok result) : ∃ input, value = .ok input ∧ next input = .ok result := by
  cases value with
  | error _ => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

theorem mapM_reflect {α : Type} (build : α → Except String Pattern) (predicate : α → Prop)
    (reflect : ∀ value pattern, build value = .ok pattern → predicate value)
    (values : List α) (patterns : List Pattern) (built : values.mapM build = .ok patterns) :
    ∀ value ∈ values, predicate value := by
  induction values generalizing patterns with
  | nil => simp
  | cons first rest ih =>
    rw [List.mapM_cons] at built
    obtain ⟨head, headRead, later⟩ := bind_ok built
    obtain ⟨tail, tailRead, _⟩ := bind_ok later
    intro value member
    rcases List.mem_cons.mp member with rfl | inside
    · exact reflect value head headRead
    · exact ih tail tailRead value inside

theorem scalar_reflect (row : ScalarCore.Row) (character : Char) (pattern : Pattern)
    (built : scalar? (ScalarCore.lexicalState row).resultSort character = .ok pattern) : Allowed row character := by
  unfold scalar? at built
  rw [CorePrinter.lexical_row_exact] at built
  dsimp only at built
  split at built
  · assumption
  · cases built

theorem identifier_tail_reflect (characters : List Char) (pattern : Pattern)
    (built : identifierTail? characters = .ok pattern) :
    characters ≠ [] ∧ ∀ character ∈ characters, Allowed ⟨2, by decide⟩ character := by
  induction characters generalizing pattern with
  | nil => cases built
  | cons first rest ih =>
    refine ⟨by simp, ?_⟩
    cases rest with
    | nil =>
      obtain ⟨head, headRead, _⟩ := bind_ok built
      intro character member
      cases List.mem_singleton.mp member
      exact scalar_reflect ⟨2, by decide⟩ first head headRead
    | cons second tail =>
      obtain ⟨head, headRead, later⟩ := bind_ok built
      obtain ⟨body, bodyRead, _⟩ := bind_ok later
      intro character member
      rcases List.mem_cons.mp member with rfl | inside
      · exact scalar_reflect ⟨2, by decide⟩ character head headRead
      · exact (ih body bodyRead).2 character inside

theorem identifier_reflect (name : String) (pattern : Pattern) (built : identifier? name = .ok pattern) : Identifier name := by
  have notReserved := identifier_not_reserved name pattern built
  refine ⟨notReserved, ?_⟩
  cases chars : name.toList with
  | nil => simp [identifier?, notReserved, chars] at built
  | cons first rest =>
    cases rest with
    | nil =>
      simp only [identifier?, notReserved, chars] at built
      obtain ⟨head, headRead, _⟩ := bind_ok built
      exact scalar_reflect ⟨0, by decide⟩ first head headRead
    | cons second tail =>
      simp only [identifier?, notReserved, chars] at built
      obtain ⟨head, headRead, later⟩ := bind_ok built
      obtain ⟨body, bodyRead, _⟩ := bind_ok later
      exact ⟨scalar_reflect ⟨1, by decide⟩ first head headRead, (identifier_tail_reflect _ body bodyRead).2⟩

theorem qualified_reflect (names : List String) (pattern : Pattern) (built : qualifiedName? names = .ok pattern) :
    Qualified names := by
  induction names generalizing pattern with
  | nil => cases built
  | cons first rest ih =>
    refine ⟨by simp, ?_⟩
    cases rest with
    | nil =>
      obtain ⟨head, headRead, _⟩ := bind_ok built
      intro name member
      cases List.mem_singleton.mp member
      exact identifier_reflect first head headRead
    | cons second tail =>
      obtain ⟨head, headRead, later⟩ := bind_ok built
      obtain ⟨body, bodyRead, _⟩ := bind_ok later
      intro name member
      rcases List.mem_cons.mp member with rfl | inside
      · exact identifier_reflect name head headRead
      · exact (ih body bodyRead).2 name inside

theorem symbol_reflect (characters : List Char) (pattern : Pattern)
    (built : symbolBody? characters = .ok pattern) : ∀ character ∈ characters, character.toNat ≠ 0 := by
  induction characters generalizing pattern with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨tail, tailRead, later⟩ := bind_ok built
    have tailAllowed := ih tail tailRead
    have firstAllowed : first.toNat ≠ 0 := by
      intro zero
      have same : first = '\x00' := Char.toNat_inj.mp zero
      subst first
      have refused : scalar? "DlStringScalar" '\x00' = .error "character is outside lexical sort DlStringScalar" := by
        decide +kernel
      simp [symbolBody?, tailRead, escapeLabel?, refused, bind, Except.bind] at built
    intro character member
    rcases List.mem_cons.mp member with rfl | inside
    · exact firstAllowed
    · exact tailAllowed character inside

theorem value_reflect (value : Mettapedia.Languages.Datalog.Value) (pattern : Pattern)
    (built : value? value = .ok pattern) : ValueAdmitted value := by
  cases value with
  | symbol contents =>
    obtain ⟨source, read, _⟩ := bind_ok built
    exact symbol_reflect contents.toList source read
  | number number =>
    by_cases width : Mettapedia.Languages.Datalog.Value.fits64 (.number number) = true
    · simpa only [Mettapedia.Languages.Datalog.Value.fits64, decide_eq_true_eq, ValueAdmitted] using width
    · simp [value?, width, bind, Except.bind] at built
  | unsigned number =>
    by_cases width : Mettapedia.Languages.Datalog.Value.fits64 (.unsigned number) = true
    · simpa only [Mettapedia.Languages.Datalog.Value.fits64, decide_eq_true_eq, ValueAdmitted] using width
    · simp [value?, width, bind, Except.bind] at built
  | floating _ => cases built

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
