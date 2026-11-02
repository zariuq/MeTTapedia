import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LanguageEquality

/-!
# Controls for the format's faithful spellings

Each row of a `LanguageDef` has a spelling that reads back as itself:
- an anonymous binder `^.p`, its bound variable `#0`;
- an abstraction parameter without a binder name `^body:[Name -> Proc]`;
- the substitution for an open body's bound variable `[z/#0]body`;
- a separator item `sep("|")`;
- a collection algebra `![flatten, unit "Nil"]`;
- a binder whose body is a collection `^x. {…}`, a space before the body;
- equations under their names.

A module is read under the names it is written with (`elaborateAuthored`), and under the names that carry their
instance by the module algebra (`elaborate`). A constructor whose collection kind another constructor shares keeps its
label, unless it is declared bare (`![bare]`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.FaithfulSpellingControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open scoped Commands

Module Spell {
  Theory Spell() {
    Types { Proc; Name; Guard; }
    Terms {
      "Nil" .  |- "0" : Proc;
      "Par" . ps:HashBag(Proc) |- "{" ps sep("|") "}" : Proc ![bare, flatten, unit "Nil"];
      "Sum" . gs:HashBag(Guard) |- "[" gs sep("+") "]" : Proc ![wrapped];
      "Inp" . x:Name, ^body:[Name -> Proc] |- x "(" ")" "." body : Proc;
      "Nu" . ^body:[Name -> Proc] |- "ν" body : Proc;
    }
    Equations {
      "Drop" .  |- "Nu"(^."Nil") = "Nil";
      "Swap" . P:Proc |- "Nu"(^x0."Nu"(^x1.P)) = "Nu"(^x1."Nu"(^x0.P));
      "Ext" . P:Proc, rest:HashBag(Proc) |- {"Nu"(^x0.P), ...rest} = "Nu"(^x0. {P, ...rest});
    }
    Rewrites {
      "Comm" . x:Name, body:Proc, z:Name |- {"Inp"(x, ^.body), "Out"(x, z), ...rest} ~> {[z/#0]body, ...rest};
      Cong : if S ~> T then "Nu"(^.S) ~> "Nu"(^.T);
    }
  }
  theory Spell()
}

#module_roundtrip Spell

def spell : LanguageDef :=
  match elaborateAuthored Spell.library Spell.module with
  | .ok language => language
  | .error _ => LanguageDef.empty "failed"

/-! ## Names -/

#guard spell.name == "Spell"
#guard spell.equations.map (·.name) == ["Drop", "Swap", "Ext"]
-- The module algebra's names carry the instance.
#guard (Spell.language.toOption.map fun language => language.equations.map (·.name)) == some ["Drop@0", "Swap@0", "Ext@0"]

/-! ## Rows -/

#guard (spell.terms[1]?.map (·.syntaxPattern)).map (fun items => match items with
  | [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"] => true
  | _ => false) == some true
#guard (spell.terms[1]?.map (·.algebra?)) == some (some { flatten := true, unit := some "Nil" })
#guard (spell.terms[3]?.map (·.params)) ==
  some [.simple "x" (.base "Name"), .abstractionNamed none "body" (.arrow (.base "Name") (.base "Proc"))]
#guard (spell.equations[0]?.map (·.left)) == some (.apply "Nu" [.lambda none (.apply "Nil" [])])
#guard (spell.equations[2]?.map (·.right)) ==
  some (.apply "Nu" [.lambda (some "x0") (.collection .hashBag [.fvar "P"] (some "rest"))])
#guard (spell.rewrites[0]?.map (·.left)) == some (.collection .hashBag
  [.apply "Inp" [.fvar "x", .lambda none (.fvar "body")], .apply "Out" [.fvar "x", .fvar "z"]] (some "rest"))
#guard (spell.rewrites[0]?.map (·.right)) == some (.collection .hashBag [.subst (.fvar "body") (.fvar "z")] (some "rest"))

/-! ## Representation: declared, or protected -/

-- `Par` is declared bare, so it stays bare beside the wrapped `Sum`, which shares its collection kind.
#guard (spell.terms.map (·.collectionRepresentation)) == [.bare, .bare, .wrapped, .bare, .bare]
#guard (Spell.module.theories.head?.map fun declared => match declared.body with
  | .extend _ (_ :: .terms _ bare :: _) => bare
  | _ => []) == some ["Par"]

Module Protected {
  Theory Protected() {
    Types { Proc; Guard; }
    Terms {
      "Nil" .  |- "0" : Proc;
      "Par" . ps:HashBag(Proc) |- "{" ps sep("|") "}" : Proc ![flatten, unit "Nil"];
      "Sum" . gs:HashBag(Guard) |- "[" gs sep("+") "]" : Proc ![wrapped];
    }
  }
  theory Protected()
}

#module_roundtrip Protected

Module Delimited {
  Theory Delimited() {
    Types { Term; }
    Terms {
      "Leaf" .  |- "leaf" : Term;
      "Node" . kids:Vec(Term) |- "node" kids.*delim("(", ")") : Term;
    }
  }
  theory Delimited()
}

#module_roundtrip Delimited

-- The delimiter reads back as a delimiter, after its nonterminal.
#guard (Delimited.language.toOption.bind fun language => language.terms[1]?.map fun rule =>
    match rule.syntaxPattern with
    | [.terminal "node", .nonTerminal "kids", .delimiter "(" ")"] => true
    | _ => false) == some true

-- Undeclared, `Par` keeps its label where `Sum` shares its collection kind.
#guard (Protected.language.toOption.map fun language => language.terms.map (·.collectionRepresentation)) ==
  some [.bare, .wrapped, .wrapped]

/-! ## Printed spellings, and what each is not -/

#guard Printer.pattern [] (.lambda none (.bvar 0)) == "^.#0"
#guard Printer.pattern [] (.lambda (some "y") (.bvar 0)) == "^y.y"
#guard Printer.pattern [] (.lambda none (.bvar 0)) != Printer.pattern [] (.lambda (some "x0") (.bvar 0))
#guard Printer.pattern [] (.lambda none (.collection .hashBag [] none)) == "^. {}"
#guard Printer.pattern [] (.subst (.fvar "b") (.fvar "a")) == "[? \"a\"/#0]? \"b\""
#guard Printer.pattern [] (.subst (.fvar "b") (.fvar "a")) != Printer.pattern [] (Pattern.eval (.fvar "b") (.fvar "a"))
#guard Printer.syntaxItem (.separator "|") == "sep(\"|\")"
#guard Printer.syntaxItem (.separator "|") != Printer.syntaxItem (.terminal "|")
#guard Printer.syntaxItems [.nonTerminal "args", .delimiter "(" ")"] == ["args.*delim(\"(\", \")\")"]
#guard Printer.syntaxItems [.nonTerminal "args", .delimiter "(" ")"] !=
  Printer.syntaxItems [.nonTerminal "args", .terminal "(", .terminal ")"]
#guard Printer.algebra (some { flatten := false, unit := some "U" }) == " ![unit \"U\"]"
#guard Printer.algebra none == ""
#guard Printer.algebra none (bare := true) == " ![bare]"
#guard Printer.algebra (some { flatten := true, unit := some "N" }) (bare := true) == " ![bare, flatten, unit \"N\"]"
#guard Printer.generatedEquationName "T:equation:3" && !Printer.generatedEquationName "Swap" &&
  !Printer.generatedEquationName "T:equation:x"

/-! ## The spellings, kernel-checked: each, and what it is not -/

theorem separator_spelling : Printer.syntaxItem (.separator "|") = "sep(\"|\")" := by decide +kernel

theorem separator_not_terminal : Printer.syntaxItem (.separator "|") ≠ Printer.syntaxItem (.terminal "|") := by
  decide +kernel

theorem delimiter_spelling :
    Printer.syntaxItems [.nonTerminal "args", .delimiter "(" ")"] = ["args.*delim(\"(\", \")\")"] := by
  decide +kernel

theorem delimiter_not_terminals :
    Printer.syntaxItems [.nonTerminal "args", .delimiter "(" ")"] ≠
      Printer.syntaxItems [.nonTerminal "args", .terminal "(", .terminal ")"] := by
  decide +kernel

theorem anonymous_parameter_spelling :
    Printer.termParam (.abstractionNamed none "body" (.base "Proc")) = "^body:[Proc]" := by decide +kernel

theorem anonymous_parameter_not_named :
    Printer.termParam (.abstractionNamed none "body" (.base "Proc")) ≠
      Printer.termParam (.abstractionNamed (some "x") "body" (.base "Proc")) := by decide +kernel

theorem bare_algebra_spelling :
    Printer.algebra (some { flatten := true, unit := some "N" }) (bare := true) = " ![bare, flatten, unit \"N\"]" := by
  decide +kernel

theorem undeclared_not_bare :
    Printer.algebra (some { flatten := true, unit := some "N" }) ≠
      Printer.algebra (some { flatten := true, unit := some "N" }) (bare := true) := by decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleSource.FaithfulSpellingControls
