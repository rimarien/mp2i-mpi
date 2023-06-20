(* La fonction parse prend en entrée une string et renvoie la regex
 * correspondante.
 * Epsilon est représenté par le caractère & et Vide par le caractère #.
 * On a les règles de priorité usuelles, et les espaces sont ignorés.
 *)

let parse string =
  let open Printf in
  let s = Stream.of_string string in
  let rec peek () =
    match Stream.peek s with
    | Some ' ' -> Stream.junk s; peek ()
    | Some c -> Some c
    | None -> None in
  let eat x =
    match peek () with
    | Some y when y = x -> Stream.junk s; ()
    | Some y -> failwith (sprintf "expected %c, got %c" x y)
    | None -> failwith "incomplete" in
  let rec regex () =
    let t = term () in
    match peek () with
    | Some '|' -> eat '|'; Somme (t, regex ())
    | _ -> t
  and term () =
    let f = factor () in
    match peek () with
    | None | Some ')' | Some '|' -> f
    | _ -> Produit (f, term ())
 and factor () =
    let rec aux acc =
      match peek () with
      | Some '*' -> eat '*'; aux (Etoile acc)
      | _ -> acc in
    aux (base ())
  and base () =
    match peek () with
    | Some '(' -> eat '('; let r = regex () in eat ')'; r
    | Some '&' -> eat '&'; Epsilon
    | Some '#' -> eat '#'; Vide
    | Some (')' | '|' | '*' as c) -> failwith (sprintf "unexpected '%c'" c)
    | Some c -> eat c; Lettre c
    | None -> failwith "unexpected end of string" in
  let r = regex () in
  try Stream.empty s; r
  with _ -> failwith "trailing ')' ?"

type partie_principale =
  | L of char
  | E of partie_principale
  | S of partie_principale * partie_principale
  | P of partie_principale * partie_principale

type forme_normale =
  | V
  | Eps
  | R of partie_principale
  | PlusEps of partie_principale


type regex =
  | Vide
  | Epsilon
  | Lettre of char
  | Somme of regex * regex
  | Produit of regex * regex
  | Etoile of regex

(*fonction string_of_regex, qui doit vérifier parse (string_of_regex e) = e
(mais peut utiliser plus de parenthèses que nécessaire*)

let rec string_of_regex regex = 
  match regex with
  |Vide -> "#"
  |Epsilon -> "&"
  |Lettre a -> String.make 1 a
  |Somme (s1,s2) -> "(" ^ string_of_regex s1 ^ "|" ^ string_of_regex s2 ^ ")"
  |Produit (f1,f2) -> "(" ^ string_of_regex f1 ^  string_of_regex f2 ^ ")"
  |Etoile e' -> string_of_regex e' ^ "*"

(*fonction est_vide qui prend en entrée un objet de type regex et renvoie un
booléen indiquant si le langage associé à l’expression est vide.
*)

let rec est_vide regex = 
  match regex with
  |Vide -> true
  |Etoile _ | Epsilon | Lettre _ -> false
  |Somme (s1,s2) -> est_vide s1 && est_vide s2
  |Produit (f1,f2) -> est_vide f1 || est_vide f2
  
(*fonction un_mot telle que l’appel un_mot e renvoie Some s, où s est un mot
(quelconque) du langage de e si ce langage est non vide, et None si le langage est vide.
*)

let rec un_mot e = 
  match e with
  |Vide -> None
  |Epsilon | Etoile _ -> Some ""
  |Lettre l -> Some (String.make 1 l)
  |Somme (s1,s2) -> 
    begin match un_mot s1 with
      |None -> un_mot s2
      |Some str -> Some str
    end
  |Produit (f1,f2) ->
    begin match un_mot f1, un_mot f2 with
      |Some str1,Some str2 -> Some (str1 ^ str2)
      |_ -> None
    end


(*fonction un_mot_exc ayant la même spécification que un_mot, sauf qu’elle lèvera
l’exception EstVide si le langage de l’expression est vide, et renverra un mot s du langage
sinon.*)

exception EstVide

let rec un_mot_exc reg = 
  match reg with 
  |Vide -> raise EstVide
  |Epsilon | Etoile _ -> ""
  |Lettre l -> String.make 1 l
  |Produit (f1,f2) -> un_mot_exc f1 ^ un_mot_exc f2
  |Somme (s1,s2) ->
    (try 
      un_mot_exc s1
    with
    |EstVide -> un_mot_exc s2)


(*fonction extrait_vide prenant en entrée une expression régulière e et renvoyant e' équivalente à e telle que e'
ne contienne pas le constructeur Vide, ou bien soit réduite
au constructeur Vide*)

let rec extrait_vide reg = 
  match reg with
  |Vide -> Vide
  |Epsilon -> Epsilon
  |Lettre c -> Lettre c
  |Etoile e ->
    begin match extrait_vide e with
    |Vide -> Epsilon
    |e' -> Etoile e'
    end
  |Produit (f1,f2) -> 
    begin match extrait_vide f1, extrait_vide f2 with 
    |Vide, _ | _, Vide -> Vide
    |f,f' -> Produit(f,f')
  end
  |Somme (s1,s2) ->
    begin match extrait_vide s1, extrait_vide s2 with
      |Vide,f | f,Vide -> f
      |f,f' -> Somme(f,f')
    en

(*fonction longueur_max prenant en entrée une expression régulière e et renvoyant
max{|u| | u ∈ L(e)}. On renverra AucunMot si L(e) = ∅ et NonBorne si L(e) contient des mots
arbitrairement longs.*)

let rec longueur_max = function
    | Vide -> AucunMot
    | Epsilon -> Entier 0
    | Lettre _ -> Entier 1
    | Somme (e, f) ->
    begin match longueur_max e, longueur_max f with
        | NonBorne, _ | _, NonBorne -> NonBorne
        | AucunMot, x | x, AucunMot -> x
        | Entier x, Entier y -> Entier (max x y)
    end
    | Produit (e, f) ->
    begin match longueur_max e, longueur_max f with
        | AucunMot, _ | _, AucunMot -> AucunMot
        | NonBorne, _ | _, NonBorne -> NonBorne
        | Entier x, Entier y -> Entier (x + y)
    end
    | Etoile e ->
    begin match longueur_max e with
        | AucunMot | Entier 0 -> Entier 0
        | _-> NonBorne
    end

(*fonction reduire qui prend en entrée une expression régulière e et renvoie une
expression régulière e′ en forme réduite telle que e′ ≡ e. *)


type partie_principale =
    | L of char (* lettre *)
    | E of partie_principale (* etoile *)
    | S of partie_principale * partie_principale (* somme *)
    | P of partie_principale * partie_principale (* produit *)


type forme_reduite =
    | V (* vide *)
    | Eps (* epsilon *)
    | R of partie_principale (* e (sans vide ni epsilon) *)
    | PlusEps of partie_principale (* e|epsilon *)

let rec reduire = function
    | Vide -> V
    | Epsilon -> Eps
    | Lettre c -> R (L c)
    | Etoile e ->
    begin
        match reduire e with
        | V -> Eps
        | Eps -> Eps
        | R e' -> R (E e')
        | PlusEps e' -> R (E e')
        end
    | Somme (e, e') ->
    begin
        match reduire e, reduire e' with
        | V, f | f, V -> f
        | Eps, Eps -> Eps
        | Eps, R f | R f, Eps -> PlusEps f
        | PlusEps f, R f' | R f', PlusEps f -> PlusEps (S (f, f'))
        | PlusEps f, Eps | Eps, PlusEps f -> PlusEps f
        | PlusEps f, PlusEps f' -> PlusEps (S (f, f'))
        | R f, R f' -> R (S (f, f'))
    end
    | Produit (e, e') ->
    begin
        match reduire e, reduire e' with
        | V, _ | _, V -> V
        | Eps, f | f, Eps -> f
        | PlusEps f, PlusEps f' -> PlusEps (S (f, S (f', P (f, f'))))
        | R f, PlusEps f' -> R (S (P (f, f'), f))
        | PlusEps f, R f' -> R (S (P (f', f'), f'))
        | R f, R f' -> R (P (f, f'))
    end