import Mettapedia.Languages.TuringMachine.LanguageDef
import Mettapedia.Languages.TuringMachine.Steps
import Mettapedia.Languages.TuringMachine.NotInteractive
import Mettapedia.Languages.TuringMachine.OneSort
import Mettapedia.Languages.TuringMachine.Hosted
import Mettapedia.Languages.TuringMachine.Configurations
import Mettapedia.Languages.TuringMachine.ClassicMachines
import Mettapedia.Languages.TuringMachine.NativeTypes
import Mettapedia.Languages.TuringMachine.Universal

import Mettapedia.Languages.TuringMachine.MathlibBridge
import Mettapedia.Languages.TuringMachine.FinitePostCompiler
import Mettapedia.Languages.TuringMachine.FiniteControl
import Mettapedia.Languages.TuringMachine.PartrecBridge
import Mettapedia.Languages.TuringMachine.InputEncoding
import Mettapedia.Languages.TuringMachine.UniversalTable
import Mettapedia.Languages.TuringMachine.Bridges.Computability.ConditionalPrefix
import Mettapedia.Languages.TuringMachine.Bridges.Computability.Controls

/-!
# Turing machines as authored languages

A transition table authored as a `LanguageDef`, one pair of rewrites for each
row; its steps and their sorts; why it admits no interactive presentation and
how it is nevertheless hosted in an interactive theory; its configurations and
their agreement with Mathlib's tape; machines from the classic papers and
their runs; the type system generated from a table; and one language
definition, with the table in its terms, that runs every machine. The
partial-recursive compiler supplies one finite universal tape table and
undecidability of halting in both presentations. Effective conditional prefix
machines retain their binary outputs, prefix-free halting domains, and Kraft
weights through the same compiler.
-/
