import Mettapedia.Languages.Datalog.FactInputCorrespondence

/-! Fact-file controls distinguish empty streams, empty fields, nullary
facts, optional final terminators and source/file numeric profiles. -/

namespace Mettapedia.Languages.Datalog.FactInput.Controls

theorem empty_file : read? ["R"] [.symbol] "" = some [] := by decide +kernel
theorem empty_symbol : read? ["R"] [.symbol] "\n" = some [⟨["R"], [.symbol ""]⟩] := by decide +kernel
theorem duplicate_empty_symbols :
    read? ["R"] [.symbol] "\n\n" = some [⟨["R"], [.symbol ""]⟩, ⟨["R"], [.symbol ""]⟩] := by decide +kernel
theorem nullary_fact : read? ["R"] [] "\n" = some [⟨["R"], []⟩] := by decide +kernel
theorem crlf_record : read? ["R"] [.symbol] "a\r\n" = some [⟨["R"], [.symbol "a"]⟩] := by decide +kernel
theorem unterminated_record : read? ["R"] [.symbol] "a" = some [⟨["R"], [.symbol "a"]⟩] := by decide +kernel
theorem extra_columns : read? ["R"] [.symbol] "a\tb\n" = some [⟨["R"], [.symbol "a"]⟩] := by decide +kernel
theorem empty_last_field : read? ["R"] [.number, .symbol] "1\t\n" = some [⟨["R"], [.number 1, .symbol ""]⟩] := by decide +kernel
theorem decimal_number : read? ["R"] [.number] " +010\n" = some [⟨["R"], [.number 10]⟩] := by decide +kernel
theorem hexadecimal_unsigned : read? ["R"] [.unsigned] "0x10\n" = some [⟨["R"], [.unsigned 16]⟩] := by decide +kernel
theorem binary_unsigned : read? ["R"] [.unsigned] "0b10\n" = some [⟨["R"], [.unsigned 2]⟩] := by decide +kernel
theorem hexadecimal_signed_refused : read? ["R"] [.number] "0x10\n" = none := by decide +kernel
theorem missing_field_refused : read? ["R"] [.number, .symbol] "1\n" = none := by decide +kernel
theorem blank_number_refused : read? ["R"] [.number] "\n" = none := by decide +kernel
theorem signed_overflow_refused : read? ["R"] [.number] "9223372036854775808\n" = none := by decide +kernel
theorem unsigned_overflow_refused : read? ["R"] [.unsigned] "18446744073709551616\n" = none := by decide +kernel
theorem float_refused : read? ["R"] [.floating] "1.0\n" = none := by decide +kernel

end Mettapedia.Languages.Datalog.FactInput.Controls
