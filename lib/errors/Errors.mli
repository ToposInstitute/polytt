module Code : module type of Code
module Span : module type of Asai.Span
module Logger : Asai.Logger.S with module Code := Code
