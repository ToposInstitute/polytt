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

let neg_ap_or_atomic neg fns =
  match fns with
  | None -> unlocate neg
  | Some fns -> CS.NegAp (neg, fns)
%}

%token <int> NUMERAL
%token <bool> FLAG
%token <string> ATOM
%token <string> LABEL
%token COLON COLON_COLON COLON_EQUALS COMMA SEMICOLON RIGHT_ARROW LEFT_ARROW UNDERSCORE EQUALS QUESTION BANG
(* Symbols *)
%token FORALL EXISTS LAMBDA LET IN LET_MINUS LAMBDA_MINUS RETURN DONE
%token TIMES FST SND
%token NAT ZERO SUCC NAT_ELIM
%token POLY BASE FIB RIGHT_THICK_ARROW
%token LEFT_SQUIGGLY_ARROW RIGHT_SQUIGGLY_ARROW CIRC
%token HASH
(* Delimiters *)
%token LPR RPR LSQ RSQ LBR RBR
(* Keywords *)
%token TYPE
%token REFL
(* Commands *)
%token DEF FAIL NORMALIZE PRINT DEBUG QUIT
%token EOF

%right COLON COMMA
%right RIGHT_ARROW TIMES IN
%left CIRC
%nonassoc RIGHT_THICK_ARROW

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
  | tm = plain_unannotated_term
    { tm }
  | tm = term; COLON; ty = term;
    { CS.Anno (tm, ty) }

plain_unannotated_term:
  | tms = nonempty_list(atomic_term)
    { ap_or_atomic tms }
  | EXISTS; LPR; names = nonempty_list(name); COLON; base = term; RPR; COMMA; fam = term
    { CS.Sigma (names, base, fam) }
  | base = term; TIMES; fam = term
    { CS.Sigma ([`Anon], base, fam) }
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
  | BASE; p = atomic_term
    { CS.Base p }
  | FIB; p = atomic_term; i = atomic_term
    { CS.Fib (p, i) }
  | tm = let_binding
    { tm }
  | tm = arrow
    { tm }

let_binding:
  | LET; nm = name; COLON_EQUALS; tm1 = term; IN; tm2 = term
    { CS.Let (nm, tm1, tm2) }
  | LET; nm = name; COLON; ty1 = term; COLON_EQUALS; tm1 = term; IN; tm2 = term
    { CS.Let (nm, { node = Anno(tm1, ty1) ; loc = get_loc tm1 }, tm2) }

labeled_field(sep):
  | label = LABEL; sep; term = term;
    { (label, term) }

arrow:
  | LAMBDA; nms = nonempty_list(name); RIGHT_ARROW; tm = term
    { CS.Lam(nms, tm) }
  | FORALL; LPR; names = nonempty_list(name); COLON; base = term; RPR; COMMA; fam = term
    { CS.Pi (names, base, fam) }
  | base = term; RIGHT_ARROW; fam = term
    { CS.Pi ([`Anon], base, fam) }
  | LAMBDA; pos = name; neg = name; RIGHT_SQUIGGLY_ARROW; body = hom_body
    { CS.HomLam(pos, neg, body) }
  | p = term; RIGHT_THICK_ARROW; q = term
    { CS.Hom (p, q) }

hom_body:
  | t = located(plain_hom_body)
    { t }

plain_hom_body:
  | neg = neg_term; LEFT_ARROW; tm = term; SEMICOLON; hom = hom_body
    { CS.Set (tm, neg, hom) }
  | LET; LPR; pos_name = name; LEFT_SQUIGGLY_ARROW; neg_name = name; RPR; COLON_EQUALS; hom = atomic_term; LPR; pos = term; LEFT_SQUIGGLY_ARROW; neg = neg_term; RPR; SEMICOLON; body = hom_body
    { CS.HomAp (pos, neg, hom, pos_name, neg_name, body) }
  | LET_MINUS; LPR; a_name = name; COMMA; b_name = name; RPR; COLON_EQUALS; p = neg_term; SEMICOLON; body = hom_body
    { CS.NegUnpack (p, a_name, b_name, body) }
  | LET; nm = name; COLON_EQUALS; tm = term; SEMICOLON; hom = hom_body
    { CS.Let (nm, tm, hom) }
  | LET_MINUS; nm = name; COLON_EQUALS; tm = neg_term; SEMICOLON; hom = hom_body
    { CS.NegLet (nm, tm, hom) }
  | RETURN; pos = term; LEFT_SQUIGGLY_ARROW; neg = neg_term
    { CS.Return (pos, neg) }

program:
  | t = located(plain_program)
    { t }

plain_program:
  | neg = neg_term; LEFT_ARROW; tm = term; SEMICOLON; hom = program
    { CS.Set (tm, neg, hom) }
  | LET; LPR; pos_name = name; LEFT_SQUIGGLY_ARROW; neg_name = name; RPR; COLON_EQUALS; hom = atomic_term; LPR; pos = term; LEFT_SQUIGGLY_ARROW; neg = neg_term; RPR; SEMICOLON; body = program
    { CS.HomAp (pos, neg, hom, pos_name, neg_name, body) }
  | LET_MINUS; LPR; a_name = name; COMMA; b_name = name; RPR; COLON_EQUALS; p = neg_term; SEMICOLON; body = program
    { CS.NegUnpack (p, a_name, b_name, body) }
  | LET; nm = name; COLON_EQUALS; tm = term; SEMICOLON; hom = program
    { CS.Let (nm, tm, hom) }
  | LET_MINUS; nm = name; COLON_EQUALS; tm = neg_term; SEMICOLON; hom = program
    { CS.NegLet (nm, tm, hom) }
  | DONE
    { CS.Done }

neg_spine:
  | CIRC; tms = separated_nonempty_list(CIRC, atomic_term)
    { tms }

neg_term:
  | t = located(plain_neg_term)
    { t }

plain_neg_term:
  | neg = atomic_neg_term; tms = option(neg_spine)
    { neg_ap_or_atomic neg tms }
  | LAMBDA_MINUS; LPR; nm = name; COLON; tp = term; RPR RIGHT_ARROW; prog = program
    { CS.NegLam (nm, tp, prog) }

atomic_neg_term:
  | t = located(plain_atomic_neg_term)
    { t }

plain_atomic_neg_term:
  | LPR; tm = plain_neg_term; RPR
    { tm }
  | LPR; a = neg_term; LEFT_ARROW; a_name = name; COMMA; b = neg_term; RPR
    { CS.NegPair (a, a_name, b) }
  | LPR; a = neg_term; COMMA; b = neg_term; RPR
    { CS.NegPairSimple (a, b) }
  | path = path
    { CS.Var path }
  | BANG
    { CS.Drop }

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
  | SUCC
    { CS.Succ }
  | n = NUMERAL
    { CS.Lit n }
  | TYPE
    { CS.Univ }
  | POLY
    { CS.Poly }
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
