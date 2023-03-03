# PolyTT

<p align="center">
  <img src="./poly.png" />
</p>

An implementation of [Polynomial Functors](https://topos.site/poly-book.pdf) on top of Martin-Lof Type Theory.

For examples, see `examples/` directory.

# Building

On Mac you can install `opam` with `homebrew` via:
```bash
$ brew install opam
```

A `shell.nix` file is provided to give access to `opam`:
```bash
$ nix-shell
```

Once you have `opam` you can install all the dev dependencies and then build `polytt`:

```bash
$ opam init
$ opam switch create . ocaml-base-compiler.5.0.0
$ opam install
$ dune build
```

# Running

```bash
$ dune exec polytt examples/prelude.poly
```
