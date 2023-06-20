(*
COCKE-YOUNGER-KASAMI algorithm
Pseudo-code (Q6) 
---------------------------------------------------------------------------------------------------------------
fonction CYK(g,w)
  si w = mot_vide : renvoyer S -> mot_vide
  n = longueur du mot 
  k = nombre de variables
  t = tableau (n + 1) * n * k init à false 
  pour chaque règle Xi -> a faire 
    pour d = 0 à n - 1 faire
      si w[d] = a alors t[1,d,i] = true 
  pour l = 2 à n faire 
    pour d = 0 à n - l faire
     pour l' = 0 à l - 1 faire 
      pour chaque règle de la forme X_i -> X_jX_k faire 
        t[l,d,i] <- t[l,d,i] || ( t[l',d,i] && t[l - l', d + l',i])
  
  renvoyer t[n,0,g.initial]
--------------------------------------------------------------------------------------------------------------
*)

type regle_unitaire = int * char
type regle_binaire = int * int * int

type cnf = {
  initial :int;
  nb_variables : int;
  unitaires : regle_unitaire list;
  binaires : regle_binaire list;
  mot_vide : bool
}

type arbre = 
  |Unaire of int * char 
  |Binaire of int * arbre * arbre


let g0 = {
 initial = 0;
 nb_variables = 5;
 unitaires = [(0,'b');(1,'a');(2, 'b');(4,'a')];
 binaires = [(0,1,2); (0,2,1); (0,3,1); (1,1,4); (3,1,2)];
 mot_vide = false
}

(*fonction cyk_reconnait déterminant si un mot u (donné sous forme d’une
chaîne de caractères) appartient au langage d’une grammaire G (donné sous forme d’une variable de
type cnf.)*)

let cyk_reconnait (g : cnf) (s : string) = 
  if s = "" then true (*else it breaks the code *)
  else
  let n = String.length s in
  let k = g.nb_variables in 
  let t = Array.make_matrix (n + 1) n [||] in 

  for i = 0 to n do 
    for j = 0 to n - 1 do 
      t.(i).(j) <- Array.make k false
    done;
  done;

  
  for d = 0 to n - 1 do
    List.iter (fun (i, c) -> if c = s.[d] then t.(1).(d).(i) <- true) g.unitaires
  done;

  for l = 2 to n do 
    for d = 0 to n - 1 do
      for l' = 0 to l - 1 do
        if d + l' < n then List.iter (fun (a,b,c) -> t.(l).(d).(a) <- t.(l).(d).(a) || (t.(l').(d).(b) && t.(l - l').(d + l').(c))) g.binaires
      done;
    done;
  done;

  let result = ref false in 
  for i = 0 to k - 1 do
    result := !result || t.(n).(0).(i)
  done;
  !result


(*fonction cyk_analyse qui prend les mêmes arguments que cyk_reconnait mais
renvoie (une option sur) un arbre de dérivation possible pour le mot. On renverra None si le mot n’est
pas dans le langage*)

exception No_tree

let cyk_analyse (g : cnf) (s : string) = 
  if s = "" then raise No_tree (* else it breaks the code *)
  else
  let n = String.length s in
  let k = g.nb_variables in 
  let t = Array.make_matrix (n + 1) n [||] in 

  for i = 0 to n do 
    for j = 0 to n - 1 do 
      t.(i).(j) <- Array.make k None;
    done;
  done;

  
  for d = 0 to n - 1 do
    List.iter (fun (i, c) -> if c = s.[d] then t.(1).(d).(i) <- Some (Unaire (i,c))) g.unitaires
  done;

  for l = 2 to n do 
    for d = 0 to n - l do
      for l' = 0 to l - 1 do
        let traiter (a,b,c) = 
          match t.(l).(d).(a), t.(l').(d).(b), t.(l - l').(d + l').(c) with
          | None , Some i, Some j ->
              t.(l).(d).(a) <- Some (Binaire (a,i,j))
          | _ -> ()
        in 
        List.iter traiter g.binaires
      done;
    done;
  done;
  
  match t.(n).(0).(g.initial) with 
  | None -> raise No_tree
  | Some x -> x

(*fonction cyk_compte qui prend les mêmes arguments que cyk_reconnait et
renvoie le nombre d’arbres de dérivation du mot fourni en argument.*)

let cyk_compte (g : cnf) (s : string) = 
  let n = String.length s in
  let k = g.nb_variables in 
  let t = Array.make_matrix (n + 1) n [||] in 

  for i = 0 to n do 
    for j = 0 to n - 1 do 
      t.(i).(j) <- Array.make k 0;
    done;
  done;

  let traiter_unitaire (i,c) = 
    for j = 0 to n - 1 do 
      if s.[j] = c then t.(1).(j).(i) <- 1
    done;
  in
  List.iter traiter_unitaire g.unitaires;

  for l = 2 to n do 
    for d = 0 to n - l do
      for l' = 0 to l - 1 do
        let traiter_binaire (i,j,k) = 
          t.(l).(d).(i) <- t.(l).(d).(i) + (t.(l').(d).(j) * t.(l - l').(d + l').(k))
        in
        List.iter traiter_binaire g.binaires
      done;
    done;
  done;
  if n = 0 && g.mot_vide then 1
  else  if n = 0 then 0 
  else t.(n).(0).(g.initial)



type symbole = 
|T of char
|V of int

type regle = int * symbole list

type grammaire = {
  nb_variables : int;
  regles : regle list;
  initial : int;
}


let g1 = {
  nb_variables = 3;
  initial = 0;
  regles = [(0,[T 'a'; V 0 ; T 'b']); (0,[T 'a'; V 1 ; T 'b']); (1,[V 2; V 1]) ; (1,[]); (2,[T 'a']); (2,[T 'b'])];
}

(*toutes les fonctions correspondants aux étapes de la mise en forme normale de Chomsky*)

let start g =
    {nb_variables = g.nb_variables + 1;
    regles = (n, [V g.initial]) :: g.regles;
    initial = n
    }

let term g =
    let tab = Array.make 256 (-1) in
    let next = ref g.nb_variables in
    
    let rec traite mot =
        match mot with
        | [] -> []
        | V i :: xs -> V i :: traite xs
        | T c :: xs ->
            let i = int_of_char c in
            if tab.(i) = -1 then (tab.(i) <- !next; incr next);
            V tab.(i) :: traite xs in
    
    let transforme_regle (v, mot) =
        if List.length mot <= 1 then (v, mot)
        else (v, traite mot) in
    
    let regles' = ref (List.map transforme_regle g.regles) in
        for i = 0 to 255 do
        if tab.(i) <> -1 then (
        regles' := (tab.(i), [T (char_of_int i)]) :: !regles'
    )
    done;
    
    {nb_variables = !next;
    regles = !regles';
    initial = g.initial}

let bin g =
    let next = ref g.nb_variables in

    let rec binarise (v, droite) =
        match droite with
        | [] | [_] | [_; _] -> [(v, droite)]
        | a :: b :: xs ->
            let nv_v = !next in
            let nv_regle = (v, [a; V nv_v]) in
            incr next;
            nv_regle :: binarise (nv_v, b :: xs) in
    
    let rec traite_regles = function
        | [] -> []
        | r :: rs -> binarise r @ traite_regles rs in
    
    let regles' = traite_regles g.regles in
    {
        nb_variables = !next;
        regles = regles';
        initial = g.initial
    }


let calcul_annulables g =
    let annulables = Array.make g.nb_variables false in
    let changement = ref true in
    let traite_regle (v, droite) =
        let rec aux = function
            | [] -> changement := true; annulables.(v) <- true
            | V x :: reste when annulables.(x) -> aux reste
            | _ -> () in
        if not annulables.(v) then aux droite in
    while !changement do
        changement := false;
        List.iter traite_regle g.regles
    done;
    annulables

let del g =
    let annulables = calcul_annulables g in
    let efface v (x, y) =
        let u = ref [] in
        let f x y =
            match x with
            | V v' when annulables.(v') -> u := (v, [y]) :: !u
            | _ -> () in
        f x y;
        f y x;
        !u in
    let rec traite_regles regles =
        match regles with
        | [] -> []
        | (v, []) :: reste -> traite_regles reste
        | (v, [x]) :: reste -> (v, [x]) :: traite_regles reste
        | (v, [x; y]) :: reste ->
            efface v (x, y) @ (v, [x; y]) :: traite_regles reste
        | _ -> failwith "commencez par binariser !" in
    let regles' =
        let u =
            if annulables.(g.initial) then (g.initial, []) :: traite_regles g.regles
            else traite_regles g.regles in
        ist.sort_uniq compare u in
    {nb_variables = g.nb_variables;
    regles = regles';
    initial = g.initial}

let graphe_unitaire g =
    let n = g.nb_variables in
    let graphe = Array.make n [] in
    let traite_regle (v, droite) =
        match droite with
        | [V v'] ->
            graphe.(v) <- v' :: graphe.(v)
        | _ -> () in
    List.iter traite_regle g.regles;
    graphe

let cloture_transitive graphe =
    let n = Array.length graphe in
    let cloture = Array.make_matrix n n false in
    let calcule_ligne v =
        let vus = Array.make n false in
        let rec explore i =
            if not vus.(i) then (
                vus.(i) <- true;
                cloture.(v).(i) <- true;
                List.iter explore graphe.(v)
            ) in
        explore v in
    for v = 0 to n - 1 do
        calcule_ligne v
    done;
    cloture

let remove_unit g =
    let cloture = cloture_transitive (graphe_unitaire g) in
    let n = g.nb_variables in
    let tab_regles = Array.make n [] in
    let ajoute (v, droite) =
        match droite with
        | [V _] -> ()
        | _ -> tab_regles.(v) <-
            droite :: tab_regles.(v) in
    List.iter ajoute g.regles;
    let regles = ref [] in
    for v = 0 to n - 1 do
        for v' = 0 to n - 1 do
            if cloture.(v).(v') then (
                let f droite = regles := (v, droite) :: !regles in
                List.iter f tab_regles.(v')
            )
        done
    done;
    {initial = g.initial;
    regles = List.sort_uniq compare !regles;
    nb_variables = g.nb_variables}

(*fonction de mire en forme de Chomsky*)

let normalise g =
    let g' = g |> start |> term |> bin |> del |> remove_unit in
    let unitaires = ref [] in
    let binaires = ref [] in
    let mot_vide = ref false in
    let traite (v, droite) =
        match droite with
        | [] -> assert (v = g'.initial); mot_vide := true
        | [T c] -> unitaires := (v, c) :: !unitaires
        | [V x; V y] -> binaires := (v, x, y) :: !binaires
        | _ -> assert false in
    List.iter traite g'.regles;
    {initial = g'.initial;
    nb_variables = g'.nb_variables;
    unitaires = !unitaires;
    binaires = !binaires;
    mot_vide = !mot_vide}



let _ =
  let word = "" in 
  Printf.printf "%s\n" word;
  if cyk_reconnait g0 word then Printf.printf "Oui\n" else Printf.printf "Non\n"