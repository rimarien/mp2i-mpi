type state = int

type nfa =
  {delta : state list array array;
  accepting : bool array}

let graphviz_nfa a filename =
  let open Printf in
  let n = Array.length a.delta in
  let m = Array.length a.delta.(0) in
  let out = open_out filename in
  fprintf out "digraph a {\nrankdir = LR;\n";
  (* noms des états *)
  let lettre i = String.make 1 (char_of_int (i + int_of_char 'a')) in
  (* etats *)
  for q = 0 to n - 1 do
    let shape = if a.accepting.(q) then "doublecircle" else "circle" in
    fprintf out "node [shape = %s, label = %d] %d;\n" shape q q
  done;
  (* etat initial *)
  fprintf out "node [shape = point]; I\n";
  fprintf out "I -> %i;\n" 0;
  (* transitions *)
    let labels = Array.make_matrix n n [] in
  for q = 0 to n - 1 do
    for x = m - 1 downto 0 do
      let ajoute q' = labels.(q).(q') <- lettre x :: labels.(q).(q') in
      List.iter ajoute a.delta.(q).(x)
    done
  done;
  for q = 0 to n - 1 do
    for q' = 0 to n - 1 do
      let s = String.concat "," labels.(q).(q') in
      if s <> "" then
        fprintf out "%i -> %i [ label = \"%s\" ];\n" q q' s
    done
  done;
  fprintf out "}\n";
  close_out out

let genere_pdf input_file output_file =
  Sys.command (Printf.sprintf "dot -Tpdf %s -o %s" input_file output_file)


type 'a regex =
  | Empty
  | Eps
  | Letter of 'a
  | Sum of 'a regex * 'a regex
  | Concat of 'a regex * 'a regex
  | Star of 'a regex


(* Parses a string into an int regex.
 * The alphabet is assumed to be a subset of a..z, and is converted
 * to [0..25] (a -> 0, b -> 1...),
 * Charcater '&' stands for "epsilon", and character '#' for "empty".
 * Spaces are ignored, and the usual priority rules apply.
 *)

let parse string =
  let open Printf in
  let to_int c =
    assert ('a' <= c && c <= 'z');
    int_of_char c - int_of_char 'a' in
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
    | Some '|' -> eat '|'; Sum (t, regex ())
    | _ -> t
  and term () =
    let f = factor () in
    match peek () with
    | None | Some ')' | Some '|' -> f
    | _ -> Concat (f, term ())
 and factor () =
    let rec aux acc =
      match peek () with
      | Some '*' -> eat '*'; aux (Star acc)
      | _ -> acc in
    aux (base ())
  and base () =
    match peek () with
    | Some '(' -> eat '('; let r = regex () in eat ')'; r
    | Some '&' -> eat '&'; Eps
    | Some '#' -> eat '#'; Empty
    | Some (')' | '|' | '*' as c) -> failwith (sprintf "unexpected '%c'" c)
    | Some c -> eat c; Letter (to_int c)
    | None -> failwith "unexpected end of string" in
  let r = regex () in
  try Stream.empty s; r
  with _ -> failwith "trailing ')' ?"


let rec string_of_regex e =
  let open Printf in
  let to_char i =
    char_of_int (i + int_of_char 'a') in
  let priorite = function
    | Sum (_, _) -> 1
    | Concat (_, _) -> 2
    | Star _ -> 3
    | _ -> 4 in
  let parenthese expr parent =
    if priorite expr < priorite parent then
      sprintf "(%s)" (string_of_regex expr)
    else string_of_regex expr in
  match e with
  | Empty -> "#"
  | Eps -> "&"
  | Letter x -> sprintf "%c" (to_char x)
  | Sum (f, f') -> sprintf "%s|%s" (parenthese f e) (parenthese f' e)
  | Concat (f, f') -> sprintf "%s%s" (parenthese f e) (parenthese f' e)
  | Star f -> sprintf "%s*" (parenthese f e)


type dfa =
  {delta_d : state array array;
  accepting_d : bool array}

let to_nfa a =
  let n = Array.length a.delta_d in
  let m = Array.length a.delta_d.(0) in
  let delta = Array.make_matrix n m [] in
  for q = 0 to n - 1 do
    for x = 0 to m - 1 do
      delta.(q).(x) <- [a.delta_d.(q).(x)]
    done
  done;
  {delta = delta; accepting = a.accepting_d}

let graphviz_dfa a = graphviz_nfa (to_nfa a)


(*fonction merge qui prend en entrée deux listes u et v supposées strictement
croissantes, et renvoie une liste strictement croissante dont l’ensemble des éléments est l’union de celui
de u et de celui de v.*)

let rec merge u v = 
  match u,v with
  | [], ys -> ys
  | xs, [] -> xs
  | x :: xs, y :: ys -> 
    if x = y then x ::  (merge xs ys)
    else 
      if x < y then x :: (merge xs v)
      else y :: (merge u ys)

(*fonction qui teste si le langage dénoté par une expression est vide*)

let rec is_empty reg = 
  match reg with 
  | Empty -> true
  | Sum(x,y) -> is_empty x && is_empty y
  |Concat(x,y) -> is_empty x || is_empty y
  |_ -> false

(*fonction qui teste si ε appartient au langage dénoté par une expression régulière*)

let rec contains_epsilon reg = 
  match reg with
  |Empty | Letter _ -> false
  |Eps | Star _ -> true
  |Sum(x,y) -> contains_epsilon x || contains_epsilon y
  |Concat(x,y) -> contains_epsilon x && contains_epsilon y

(*fonction prefix qui prend en entrée une expression régulière e et renvoie
l’ensemble P associé à L(e), sous forme d’une liste strictement croissante.
*)

let rec prefix e = 
  match e with 
  | Eps | Empty -> []
  |Letter x -> [x]
  |Sum(x,y) -> merge (prefix x) (prefix y)
  |Concat(x,y) -> 
    if is_empty x || is_empty y then []
    else if contains_epsilon x then merge (prefix x) (prefix y)
    else prefix x
  |Star x -> prefix x

(*même la fonction suffix calculant l’ensemble S*)

let rec suffix e = 
  match e with
  |Eps | Empty -> []
  |Letter x -> [x]
  |Sum(x,y) -> merge (suffix x) (suffix y)
  |Concat(x,y) -> 
    if is_empty x || is_empty y then []
    else if contains_epsilon y then merge (prefix x) (prefix y)
    else prefix y
  |Star x -> suffix x

(*fonction combine qui prend en entrée deux listes [x1; ...; xn] et [y1; ...; yp]
et renvoie une liste de longueur np contenant tous les couples (xi, yj) avec 1 ⩽ i ⩽ n et 1 ⩽ j ⩽ p (l’ordre
des couples dans la liste est arbitraire*)

let rec combine u v = 
  match u with
  |[] -> []
  |x :: xs -> 
    let prod_avec_x = List.map (fun y -> (x,y)) v in 
    prod_avec_x @ combine xs v

(*fonction factor qui calcule l’ensemble F associé à une expression régulière.
*)

let rec factor reg = 
  match reg with 
  |Empty | Eps | Letter _-> []
  |Sum(x,y) -> 
    merge (factor x) (factor y)
  |Concat(x,y) -> 
    if is_empty x || is_empty y then []
    else merge (merge (factor x) (factor y)) (combine (suffix x) (prefix y))
  |Star x -> merge (factor x) (combine (suffix x) (prefix x))

(*fonction number_of_letters qui prend en entrée une 'a regex et renvoie le
nombre total de feuilles de la forme Letter x qu’elle contient*)

let rec number_of_letters reg = 
  match reg with
  |Eps | Empty -> 0
  |Letter _ -> 1
  |Star x -> number_of_letters x
  |Concat(x,y) | Sum(x,y) -> number_of_letters x + number_of_letters y

(*fonction linearize qui prend en entrée un e de type 'a regex et renvoie un e′
de type ('a * int) regex défini comme suit :
■ l’arbre e′ a exactement la même forme que e ;
■ tous ses nœuds sont inchangés, à l’exception des feuilles Letter x;
■ chaque feuille Letter x est remplacée par une feuille Letter (x, i), où i est son numéro (parmi les
feuilles) dans l’ordre préfixe (i varie donc de 1 à number_of_letters e).*)

let linearize reg = 
  let i = ref 0 in 
  let rec aux t = 
    match t with
    |Empty -> Empty
    |Eps -> Eps
    |Letter x -> incr i; Letter (x, !i)
    |Sum(x,y) -> let x' = aux x in Sum(x', aux y)
    |Concat(x,y) -> let x' = aux x in Concat(x', aux y)
    |Star x -> Star (aux x) in 
  aux reg

(*fonction max_letter prenant en entrée une int regex et renvoyant le plus
grand i tel que Letter i apparaisse dans l’expression, ou -1 si l’expression ne contient aucune lettre.*)

let rec max_letter reg = 
  match reg with 
  |Empty | Eps -> -1
  |Letter i -> i 
  |Star x -> max_letter x
  |Sum(x,y) | Concat(x,y) -> max (max_letter x) (max_letter y)

(*fonction glushkov prenant en entrée une expression régulière e de type
int regex et construisant l’automate de Glushkov associé à l’aide de l’algorithme de Berry-Sethi.*)

let glushkov reg = 
  let linearized = linearize reg in 
  let pre = prefix linearized in 
  let suf = suffix linearized in 
  let fac = factor linearized in 
  let n = number_of_letters linearized in 
  let m = max_letter reg in
  let delta = Array.make_matrix (n + 1) (m + 1) [] in 
  let accepting = Array.make (n + 1) false in 

  let f i x j = delta.(i).(x) <- j :: delta.(i).(x) in 
  List.iter( fun (x,i) -> f 0 x i) pre;
  List.iter (fun ((x,i),(y,j)) -> f i y j) fac;
  List.iter (fun (x,i) -> accepting.(i) <- true) suf;

  if contains_epsilon reg then accepting.(0) <- true;
  {delta = delta; accepting = accepting}

(*fonction delta_set spécifiée comme suit :
Arguments et préconditions :
■ le premier argument est un automate non déterministe A d’ensemble d’états Q;
■ le deuxième argument est un tableau arr de n booléens, où n = |Q|, qui spécifie une partie E de Q
(q ∈ E si et seulement si arr.(q) = true) ;
■ le troisième argument est une entier x correspondant à une lettre du langage de A (on garantit donc
0 ⩽ x < |a.delta.(0)!).
Valeur de retour : un tableau de booléens codant la partie δ(E, x) de Q.
*)

let delta_set automate set letter = 
  let n = Array.length set in 
  let new_set = Array.make n false in
  let transition s = new_set.(s) <- true in 
  for state = 0 to n - 1 do
    if set.(state) then List.iter transition automate.delta.(state).(letter)
  done;
  new_set

(*fonction has_accepting_state qui détermine si un ensemble d’états, codé par
un tableau de |Q| booléens, contient l’un au moins des états acceptants d’un automate A*)

let has_accepting_state automate set = 
  let final = automate.accepting in 
  let check = ref false in 
  let n = Array.length set in 
  for i = 0 to n - 1 do
    if final.(i) && set.(i) then check := true
  done;
  !check

(*fonction nfa_accept qui détermine si un mot, représenté par une liste d’entiers,
appartient au langage d’un automate non déterministe donné*)

let nfa_accept automate lst = 
  let n = Array.length automate.accepting in
  let rec app_delta_star set word = 
    match word with 
    |[] -> set
    |x :: xs ->
        let new_set = delta_set automate set x in 
        app_delta_star new_set xs in 
  let init = Array.make n false 
  in init.(0) <- true;
  let f = app_delta_star init lst in 
  has_accepting_state automate f

(*fonction build_set qui prend en entrée un nfa, un ensemble d’états s codé
par une liste strictement croissante, et une lettre x, et renvoie l’ensemble d’états δ(s, x), toujours codé par
une liste strictement croissante. On garantira une complexité en O(|Q| + deg+(s, x)), où deg+(s) est le nombre de transitions de la forme q
x→ q′ avec q ∈ s.*)

let build_set nfa lst letter = 
  let n = Array.length nfa.delta in 
  let next_states_present = Array.make n false in
  List.iter (fun q -> (List.iter (fun q' -> next_states_present.(q') <- true) nfa.delta.(q).(letter))) lst; 
  let next_set = ref [] in 
  for state = n - 1 downto 0 do
    if next_states_present.(state) then next_set := state :: !next_set
  done;
  !next_set

(*fonction powerset qui prend en entrée un automate non déterministe et renvoie
l’automate des parties associé. On ne construira que les états accessibles de cet automate*)

let powerset nfa = 
  let n = Array.length a.delta in
  let m = Array.length a.delta.(0) in 
  let sets = Hashtbl.create n in 
  Hashtbl.add sets [0] 0;
  let transitions = ref [] in 
  let last_dfa_state = ref 0 in (*indice du dernier state de dfa qu'on a ajouté*)

  let add_set set = (*si le set existe : renvoie false,indice du set déjà existant. sinon, renvoie true et le nouvel indice*)
    if Hashtbl.mem sets set then 
      let index = Hashtbl.find sets set in 
      true,index 
    else
      incr last_dfa_state;
      Hashtbl.add sets set !last_dfa_state
      false,!last_dfa_state
  
  let rec dfs set start = 
    for letter = 0 to m - 1 do (*On construit notre nouvel ensemble d'état pour chaque lettre potentielle, et on ajoute les transitions*) 
      let new_set = build_set nfa set letter in
      let set_already_exists, endpoint = add_set new_set in 
      transitions := (start,letter,endpoint) :: !transitions in
      if not set_already_exists then dfs new_set endpoint
    done;
  in dfs [0] 0; 
  let nb_dfa = !last_dfa_state + 1 (*on commence à 0*)
  let transitions_dfa = Array.make matrix n m (-1) in 
  List.iter (fun (start,lettre,endpoint) -> transitions_dfa.(start).(lettre) <- endpoint) !transitions;

  let rec is_ok set = 
    match set with 
    |[] -> false 
    |q :: qs -> nfa.accepting.(q) || is_accepting qs 
  in 
  let accepting_dfa = Array.make nb_dfa false in 
  Hashtbl.iter (fun etat indice -> accepting_dfa.(indice) <- is_ok etat) sets

(* fonction is_denotation qui détermine si une expression régulière dénote le
langage d’un automate*)

let is_denotation e a =
    let g' = powerset (glushkov e) in
    let a' = powerset a in
    Automates.equivalent (to_afd a') (to_afd g')


(*fonction equivalent qui détermine si deux expressions régulières sont équivalentes*)

let equivalent e f =
    is_denotation e (glushkov f)

(*fonction compute_regex qui prend en entrée un automate non déterministe et
renvoie une expression régulière dénotant son langage*)


let rec simplify = function
    | Star e ->
        begin match simplify e with
            | Star e' -> Star e'
            | Empty | Eps -> Eps
            | e' -> Star e'
        end
    | Concat (e, f) ->
    begin match simplify e, simplify f with
        | Empty, _ | _, Empty -> Empty
        | Eps, f' | f', Eps -> f'
        | e', f' -> Concat (e', f')
    end
    | Sum (e, f) ->
    begin match simplify e, simplify f with
        | Empty, f' | f', Empty -> f'
        | e', f' when e' = f' -> e'
        | e', f' -> Sum (e', f')
    end
    | e -> e

let copy_into mat1 mat2 =
    for i = 0 to Array.length mat1 - 1 do
        for j = 0 to Array.length mat1.(i) - 1 do
            mat2.(i).(j) <- mat1.(i).(j)
        done
    done


let compute_regex a =
    let n = Array.length a.delta in
    let m = Array.length a.delta.(0) in
    
    (* initialization *)
    let mat = Array.make_matrix n n Empty in
    for i = 0 to n - 1 do
        mat.(i).(i) <- Eps
    done;
    for i = 0 to n - 1 do
        for x = 0 to m - 1 do
            let ajoute_trans j = mat.(i).(j) <- Sum (Letter x, mat.(i).(j)) in
            List.iter ajoute_trans a.delta.(i).(x)
        done
    done;

    (* main loop *)
    for k = 0 to n - 1 do
        let next_mat = Array.make_matrix n n Empty in
        for i = 0 to n - 1 do
            for j = 0 to n - 1 do

                next_mat.(i).(j) <-
                    Sum (
                        mat.(i).(j),
                    Concat (
                        mat.(i).(k),
                        Concat (Star (mat.(k).(k)), mat.(k).(j))
                    ));
                next_mat.(i).(j) <- simplify next_mat.(i).(j)
            done
        done;
        copy_into next_mat mat;
    done;
    let res = ref Empty in
    for i = 0 to n - 1 do
        if a.accepting.(i) then res := Sum (mat.(0).(i), !res)
    done;
    simplify !res
