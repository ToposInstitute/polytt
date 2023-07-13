# High-Level design of PolyTT

This document details the high-level architechture of `polytt`. Note that this does
not describe the type theory; for that, see `rules.pdf`.

## The Core

We will work our way from the bottom-up, starting from the core of the implementation,
which (unsurprisingly) lives in `lib/core`.

The most important set of datatypes in `polytt` are the core terms, which are defined
in `lib/core/Data.ml`, and are re-exported in `lib/core/Domain.ml` and `lib/core/Syntax.ml`.
These consist of:
- `syn`/`Syntax.t`, which is the *syntax* of the type theory. These denote (potentially)
  unevaluated terms and types.
- `value`/`Domain.t`, which are the *value* of the type theory. As the name suggests,
  these are evaluated terms and types.

Now that we've got the datatypes out of the way, the core consists of 3 main components:
- The evaluator, (`lib/core/Semantics.ml`) evaluates `Syntax.t` into `Domain.t`
- The quoter (`lib/core/Quote.ml`) quotes `Domain.t` back into `Syntax.t`
- The conversion checker (`lib/core/Conversion.ml`) checks to see if two values are β/η-equivalent.

## The Refiner

The refiner builds on top of the core, and implements the type-checking rules for `polytt`.
It lives in `lib/refiner`. Note that this is *not* what translates surface syntax into
core syntax. Instead, it just implements the rules of the type theory, which live in
`lib/refiner/rules`.

The refiner is bidirectional and tactic based, and you can find the definition of tactics
in `lib/refiner/Tactic.ml`. It needs to handle quite a few effects (variable resolution, errors,
type holes, etc), and also needs to interface with the core. All of this can be found in
`lib/refiner/Eff.ml`.

## The Elaborator

The elaborator is responsible for transforming surface syntax (IE: what comes out of the parser)
into core syntax. It can be found in `lib/elaborator`. The definition of surface syntax lives
in `lib/elaborator/Syntax.ml`, and the interface to the elaborator can be found in 
`lib/elaborator/Elaborator.ml`. Elaboration mainly consists of a big pattern match on surface syntax,
followed by invocations of the appropriate refiner rules.

## The Vernacular

The vernacular is the main engine of user interaction, and is where we handle
commands such as defining definitions, performing imports, printing values, etc.
It can be found in `lib/vernacular`. It also has it's own suite of effects, which
are defined in `lib/vernacular/Eff.ml`. The actual interface is implemented in
`lib/vernacular/Driver.ml`, and the commands are defined in `lib/vernacular/Syntax.ml`.

## The Parser

The parser (and lexer) live in `lib/parser`. These are quite standard, so we do
not remark on them further.

## The Loader

The loader is a small shim that handles actually locating source files. It
lives in `lib/loader`. Once found, the source files are passed off to the parser,
and the resulting commands are fed to the vernacular. Note that this also handles
locating imports.

## The Actual Binary

The actual binary `polytt` lives in `bin/main.ml`, and is a small shim that does
argument parsing, and then invokes the loader.
