open Printf


type state = {
  str : string;
  mutable index : int
}

let new_state str =
  {str = str; index = 0}

exception SyntaxError

let peek s =
  if s.index < String.length s.str then Some s.str.[s.index]
  else None

let error s =
  match peek s with
  | None ->
  printf "Unexpected end of input\n";
  raise SyntaxError
  | Some c ->
  printf "Unexpected token %c at position %d\n" c s.index;
  raise SyntaxError


(*fonction expect prenant en entrée un stream s et un char c et ayant le compor-
tement suivant :
■ si le prochain caractère du flux existe et vaut c, alors la fonction passe au caractère suivant et ne
renvoie rien ;
■ sinon, elle affiche un message d’erreur comme ci-dessous puis lève l’exception SyntaxError.*)

let expect s c =
  match peek s with
  |Some c' when c' = c -> s.index <- s.index +1
  | _->printf "Unexpected end of input\n";
  raise SyntaxError

(*fonction discard qui prend en entrée un stream et passe au caractère suivant
(en ignorant le caractère actuel). On signalera l’erreur s’il n’y a pas de caractère actuel*)

let discard s =
  match peek s with
  |Some _ -> s.index <- s.index +1
  | _->printf "Unexpected end of input\n";
  raise SyntaxError

(*fonction is_letter prenant en entrée un caractère et renvoyant un booléen
indiquant si ce caractère est dans l’ensemble {a, . . . , z, A, . . . , Z}.*)

let is_letter c =
  ((int_of_char 'a') <= (int_of_char c) && (int_of_char c) <= (int_of_char 'z'))
  ||
  ((int_of_char 'A') <= (int_of_char c) && (int_of_char c) <= (int_of_char 'Z'))

type regex_ast =
  | Sum of regex_ast * regex_ast
  | Concat of regex_ast * regex_ast
  | Char of char
  | Star of regex_ast
  | Maybe of regex_ast
  | Any

(*deux fonctions d’analyse syntaxique mutuellement récursives regex et paren cor-
respondant respectivement aux variables R et P de la grammaire suivante
R → P + P | PP | P∗ | P? | . | a ∈ Σ0
P → (R)*)

let rec p s =
  match peek s with
  |Some '(' ->
    begin
      let p = paren s in
      match peek s with
      |Some '+' ->
        discard s;
        let p' = paren s in
        Sum (p, p')
      |Some '*' -> 
        discard s;
        Star p
      |Some '?' ->
        discard s;
        Maybe p
      |Some '(' ->
        let p' = paren s in
        Concat (p, p')
      |_->  printf "Unexpected end of input\n";
      raise SyntaxError
               end
  |Some '.' -> discard s;
  Any
  |Some c when is_letter c -> 
    discard s;
    Char c
  |_ -> printf "Unexpected end of input\n";
  raise SyntaxError
and paren s =
  match peek s with
  | Some '(' ->
    discard s;
    let r = p s in
    expect s ')';
    r
  | _ -> error s

(*fonction parse_regex prenant en entrée une expression régulière sous forme
d’une chaîne de caractères et renvoyant l’arbre de syntaxe abstraite correspondant.*)

let parse initial_symbol str =
  let s = new_state str in
  let tree = initial_symbol s in
  match peek s with
  | None -> tree
  | Some c -> printf "Expected input to end\n"; error s
  let parse_regex str = parse regex str

(*analyseur syntaxique en descente récursive pour votre grammaire. Cet analyseur
devrait logiquement utiliser trois fonctions mutuellement récursives de type state -> regex_ast (plus
une fonction externe).*)

let rec regex_2 s =
  let t = term s in
  match peek s with
  | Some '|' ->
  expect s '|';
  let e = regex_2 s in
  Sum (t, e)
  | _ -> t
  and term s =
  let f = factor s in
  match peek s with
  | None | Some ')' | Some '|' -> f
  | _ ->
  let t = term s in
  Concat (f, t)
  and factor s =
  match peek s with
  | Some '(' ->
  expect s '(';
  let e = regex_2 s in
  expect s ')';
  e
  | Some c when is_letter c ->
  expect s c;
  Char c
  | _ -> error s
  let parse_regex_2 str = parse regex_2 str

(*analyseur syntaxique pour la grammaire*)

let rec regex_3 s =
  let t = term s in
  match peek s with
  | Some '|' ->
  expect s '|';
  let e = regex_3 s in
  Sum (t, e)
  | _ -> t
  and term s =
  let f = factor s in
  match peek s with
  | None | Some ')' | Some '|' -> f
  | _ ->
  let t = term s in
  Concat (f, t)
  and factor s =
  let a = atom s in
  quantif s a
  and quantif s a =
  match peek s with
  | Some '*' ->
  discard s;
  quantif s (Star a)
  | Some '?' ->
  discard s;
  quantif s (Maybe a)
  | _ -> a
  and atom s =
  match peek s with
  | Some '(' ->
  expect s '(';
  let e = regex_3 s in
  expect s ')';
  e
  | Some c when is_letter c ->
  expect s c;
  Char c
  | _ -> error s
  let parse_regex_3 str = parse regex_3 str