type t =
  [ `LexError
  | `ParseError
  | `RequiresAnnotation
  | `UnboundVariable
  | `TypeError
  | `ConversionError
  | `HoleInSynth
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
