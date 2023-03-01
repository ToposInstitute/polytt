%{
open Asai

module CS = Vernacular.Syntax

let locate (start, stop) node =
  {CS.node; loc = Span.make (Span.of_lex_position start) (Span.of_lex_position stop)}

let unlocate {CS.node; loc = _} = node

let ap_or_atomic =
  function
  | [] -> failwith "Impossible Internal Error"
  | [f] -> unlocate f
  | f :: args -> CS.Ap (f, args)
%}

%token <int> NUMERAL
%token <bool> FLAG
%token <string> ATOM
%token COLON COLON_COLON COLON_EQUALS COMMA RIGHT_ARROW THICK_RIGHT_ARROW UNDERSCORE
(* Symbols *)
%token FORALL LAMBDA
%token TIMES FST SND
%token NAT ZERO SUCC NAT_ELIM
%token POLY BASE FIB HOM_BASE HOM_FIB TENSOR TENSOR_ELIM TRI FROWN_LSQ
(* Delimiters *)
%token LPR RPR LSQ RSQ
(* Keywords *)
%token TYPE
(* Commands *)
%token DEF FAIL NORMALIZE PRINT DEBUG QUIT
%token EOF

%nonassoc THICK_RIGHT_ARROW
%right RIGHT_ARROW TIMES

%start <Vernacular.Syntax.cmd list> commands

%type <Core.Ident.path>
  path
%type <Core.Ident.t>
  name
%%

%inline
located(X):
  | e = X
    { locate $loc e }

path:
  | path = separated_nonempty_list(COLON_COLON, ATOM)
    { path }

name:
  | path = path
    { `User path }
  | UNDERSCORE
    { `Anon }

commands:
  | EOF
    { [] }
  | cmd = command; cmds = commands
    { cmd :: cmds }

command:
  | c = located(plain_command)
    { c }

plain_command:
  | DEF; name = name; COLON; tp = term; COLON_EQUALS; tm = term
    { CS.Def {name; tp = Some tp; tm} }
  | DEF; name = name; COLON_EQUALS; tm = term
    { CS.Def {name; tp = None; tm} }
  | FAIL; name = name; COLON; tp = term; COLON_EQUALS; tm = term
    { CS.Fail {name; tp = Some tp; tm} }
  | FAIL; name = name; COLON_EQUALS; tm = term
    { CS.Fail {name; tp = None; tm} }
  | NORMALIZE; tm = term
    { CS.Normalize tm }
  | PRINT; tm = term
    { CS.Print tm }
  | DEBUG; b = FLAG
    { CS.Debug b }
  | QUIT
    { CS.Quit }

term:
  | t = located(plain_term)
    { t }

plain_term:
  | tms = nonempty_list(atomic_term)
    { ap_or_atomic tms }
  | LPR; name = name; COLON; base = term; RPR; TIMES; fam = term
    { CS.Sigma (name, base, fam) }
  | base = term; TIMES; fam = term
    { CS.Sigma (`Anon, base, fam) }
  | FST; tm = atomic_term
    { CS.Fst tm }
  | SND; tm = atomic_term
    { CS.Snd tm }
  | SUCC; tm = atomic_term
    { CS.Succ tm }
  | BASE; p = atomic_term
    { CS.Base p }
  | FIB; p = atomic_term; x = atomic_term
    { CS.Fib (p, x) }
  | HOM_BASE; f = atomic_term; x = atomic_term
    { CS.HomBase (f, x) }
  | HOM_FIB; f = atomic_term; x = atomic_term; qx = atomic_term
    { CS.HomFib (f, x, qx) }
  | p = atomic_term; TENSOR; q = atomic_term
    { CS.Tensor (p, q) }
  | TENSOR_ELIM; mot = atomic_term; LPR; LAMBDA; p = name; q = name; RIGHT_ARROW; bdy = term; RPR; scrut = atomic_term
    { CS.TensorElim(p, q, mot, bdy, scrut) }
  | p = atomic_term; TRI; q = atomic_term
    { CS.Tri (p, q) }
  | p = atomic_term; FROWN_LSQ; f = term; RSQ; q = atomic_term
    { CS.Frown (p, q, f) }
  | NAT_ELIM; mot = atomic_term; zero = atomic_term; succ = atomic_term; scrut = atomic_term
    { CS.NatElim (mot, zero, succ, scrut) }
  | tm = arrow
    { tm }

arrow:
  | LAMBDA; nms = list(name); RIGHT_ARROW; tm = term
    { CS.Lam(nms, tm) }
  | LPR; name = name; COLON; base = term; RPR; RIGHT_ARROW; fam = term
    { CS.Pi (name, base, fam) }
  | base = term; RIGHT_ARROW; fam = term
    { CS.Pi (`Anon, base, fam) }
  | p = term; THICK_RIGHT_ARROW; q = term
    { CS.PolyHom (p, q) }

atomic_term:
  | t = located(plain_atomic_term)
    { t }

plain_atomic_term:
  | LPR; tm = plain_term; RPR
    { tm }
  | LPR; t1 = term; COMMA; t2 = term; RPR
    { CS.Pair (t1, t2) }
  | path = path
    { CS.Var path }
  | NAT
    { CS.Nat }
  | ZERO
    { CS.Zero }
  | n = NUMERAL
    { CS.Lit n }
  | TYPE
    { CS.Univ }
  | POLY
    { CS.Poly }
