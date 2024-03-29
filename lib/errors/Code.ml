type t =
  [ `LexError
  | `ParseError
  | `RequiresAnnotation
  | `UnboundVariable
  | `TypeError
  | `ConversionError
  | `HoleInSynth
  | `NotAHom
  | `LinearVariableDoubleUse
  | `LinearVariablesNotUsed
  | `LoadFailure
  ]

let default_severity _ = Asai.Severity.Error

let to_string : t -> string =
  function
  | `LexError -> "E001"
  | `ParseError -> "E002"
  | `RequiresAnnotation -> "E003"
  | `UnboundVariable -> "E004"
  | `TypeError -> "E005"
  | `ConversionError -> "E006"
  | `HoleInSynth -> "E007"
  | `NotAHom -> "E008"
  | `LinearVariableDoubleUse -> "E009"
  | `LinearVariablesNotUsed -> "E010"
  | `LoadFailure -> "E011"
