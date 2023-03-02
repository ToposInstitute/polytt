%{
open Asai

module CS = Vernacular.Syntax

let locate (start, stop) node =
  {CS.node; loc = Span.make (Span.of_lex_position start) (Span.of_lex_position stop)}

let unlocate {CS.node; loc = _} = node
let get_loc {CS.loc; node = _} = loc


let ap_or_atomic =
  function
  | [] -> failwith "Impossible Internal Error"
  | [f] -> unlocate f
  | f :: args -> CS.Ap (f, args)
%}

%token <int> NUMERAL
%token <bool> FLAG
%token <string> ATOM
%token <string> LABEL
%token COLON COLON_COLON COLON_EQUALS COMMA DOT RIGHT_ARROW UNDERSCORE EQUALS QUESTION
(* Symbols *)
%token FORALL LAMBDA LET IN
%token TIMES FST SND
%token NAT ZERO SUCC NAT_ELIM
%token HASH
(* Delimiters *)
%token LPR RPR LSQ RSQ LBR RBR
(* Keywords *)
%token TYPE
%token REFL
(* Commands *)
%token DEF FAIL NORMALIZE PRINT DEBUG QUIT IMPORT
%token EOF

%right COLON
%right RIGHT_ARROW TIMES IN

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
  | IMPORT; name = path;
    { CS.Import {shadowing = false; unitpath = name} }
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
  | LPR; t1 = term; COMMA; t2 = term; RPR
    { CS.Pair (t1, t2) }
  | FST; tm = atomic_term
    { CS.Fst tm }
  | tm1 = atomic_term; EQUALS; tm2 = atomic_term
    { CS.Eq (tm1, tm2) }
  | REFL
    { CS.Refl }
  | SND; tm = atomic_term
    { CS.Snd tm }
  | NAT_ELIM; mot = atomic_term; zero = atomic_term; succ = atomic_term; scrut = atomic_term
    { CS.NatElim (mot, zero, succ, scrut) }
  | tm = anno
    { tm }
  | tm = let_binding
    { tm }
  | tm = arrow
    { tm }

anno:
  | tm = term; COLON; ty = term;
    { CS.Anno (tm, ty) }

let_binding:
  | LET; nm = name; EQUALS; tm1 = term; IN; tm2 = term
    { CS.Let (nm, tm1, tm2) }
  | LET; nm = name; COLON; ty1 = term; EQUALS; tm1 = term; IN; tm2 = term
    { CS.Let (nm, { node = Anno(tm1, ty1) ; loc = get_loc tm1 }, tm2) }

labeled_field(sep):
  | label = LABEL; sep; term = term;
    { (label, term) }

arrow:
  | LAMBDA; nms = list(name); RIGHT_ARROW; tm = term
    { CS.Lam(nms, tm) }
  | LPR; name = name; COLON; base = term; RPR; RIGHT_ARROW; fam = term
    { CS.Pi (name, base, fam) }
  | base = term; RIGHT_ARROW; fam = term
    { CS.Pi (`Anon, base, fam) }

atomic_term:
  | t = located(plain_atomic_term)
    { t }

plain_atomic_term:
  | LPR; tm = plain_term; RPR
    { tm }
  | path = path
    { CS.Var path }
  | NAT
    { CS.Nat }
  | ZERO
    { CS.Zero }
  | SUCC
    { CS.Succ }
  | n = NUMERAL
    { CS.Lit n }
  | TYPE
    { CS.Univ }
  | QUESTION
    { CS.Hole }
  | HASH; LBR; labels = separated_list(COMMA, LABEL); RBR;
    { CS.FinSet labels }
  | LBR; labels = separated_list(COMMA, labeled_field(EQUALS)); RBR;
    { CS.RecordLit labels }
  | label = LABEL;
    { CS.Label label }
  | LBR; labels = separated_nonempty_list(COMMA, labeled_field(COLON)); RBR;
    { CS.Record labels }
