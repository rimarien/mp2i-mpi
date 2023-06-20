type vertex = int

type graph = sommet list array

(*fonction transpose qui prend en entrée un graphe G et renvoie son graphe
transposé (ou miroir) *)

let transpose g =
    let n = Array.length g in
    let gprime = Array.make n [] in
    for i = 0 to n - 1 do
        let f j = gprime.(j) <- i :: gprime.(j) in
        List.iter f g.(i)
    done;
    gprime

(*fonction post_order qui effectue un parcours en profondeur complet d’un
graphe et renvoie la liste de ses sommets par instant de fin de traitement décroissant.
*)

let post_order g =
    let n = Array.length g in
    let post = ref [] in
    let seen = Array.make n false in
    let rec explore i =
        if not seen.(i) then begin
            seen.(i) <- true;
            List.iter explore g.(i);
            post := i :: !post
        end in
    for i = 0 to n - 1 do
        explore i
    done;
    !post

(*fonction accessible_lists qui prend en entrée un graphe G et une liste
x1, . . . , xn de sommets de G et a le comportement suivant :
L ← ()
pour i = 1 à n faire
si xi n’est pas marqué alors
Calculer les sommets acc accessibles depuis xi et les marquer (i.e. les retirer du graphe).
L ← acc, L
renvoyer L
*)

let accessible_lists gprime order =
    let n = Array.length gprime in
    let seen = Array.make n false in
    let scc_list = ref [] in
    let current_scc = ref [] in
    let rec explore i =
            if not seen.(i) then begin
            seen.(i) <- true;
            List.iter explore gprime.(i);
            current_scc := i :: !current_scc
        end in
    let process i =
        if not seen.(i) then begin
            current_scc := [];
            explore i;
            scc_list := !current_scc :: !scc_list
        end in
    List.iter process order;
    !scc_list

(*e fonction kosaraju qui prend en entrée un graphe G et renvoie la liste de ses
composantes fortement connexes*)

let kosaraju g =
    let order = post_order g in
    let gprime = transpose g in
    List.rev (accessible_lists gprime order)

(*e fonction read_graph qui lit un graphe sous ce format sur l’entrée standard.
Cette fonction pourra supposer que les sommets sont numérotés de 0 à n − 1.*)

let read_graph () =
    let n, p = Scanf.scanf "%d %d\n" (fun x y -> (x, y)) in
    let g = Array.make n [] in
    for i = 0 to p - 1 do
        Scanf.scanf "%d %d\n" (fun x y -> g.(x) <- y :: g.(x))
    done;
    g

(*programme OCaml qui lit un graphe sur l’entrée standard et affiche :
■ son nombre de composantes fortement connexes ;
■ la taille de sa plus grande composante fortement connexe.
Tester votre programme sur le fichier exemple_cours.txt et arxiv.txt.*)


let main () =
    let g = read_graph () in
    let scc_list = kosaraju g in
    let nb_components = List.length scc_list in
    let max_size =
        List.fold_left (fun acc scc -> max acc (List.length scc)) 0 scc_list in
    Printf.printf "Number of SCCs : %d\n" nb_components;
    Printf.printf "Size of largest SCC : %d\n" max_size


(*fonctions eval_litt (respectivement eval) prenant en entrée un littéral (respectivement une formule en 2-CNF) et une valuation, et renvoyant leur évaluation dans ce contexte.
*)

let eval_litt l v =
    match l with
    | P i -> v.(i)
    | N i -> not v.(i)



let rec eval f v =
    match f with
    | [] -> true
    | (l, l') :: tail ->
    (eval_litt l v || eval_litt l' v) && eval tail v



exception Last


(* fonction increment_valuation qui prend en entrée une valuation [v0, . . . , vn−1]
et renvoie la valuation suivante dans l’ordre lexicographique, ou lève l’exception Last si la valuation est
déjà maximale (vaut [true; ...; true]).*)

let increment_valuation v =
    let rec loop i =
        if i < 0 then raise Last
        else if not v.(i) then v.(i) <- true
        else begin
            v.(i) <- false;
            loop (i - 1)
        end in
    loop (Array.length v - 1)



let var = function
    | P i | N i -> i

let rec max_var = function
    | [] -> -1
    | (l, l') :: f -> max (max_var f) (max (var l) (var l'))


(* fonction brute_force qui prend en entrée une formule φ en 2-CNF et renvoie :
■ Some v, où v est un témoin de satisfiabilité de φ, s’il en existe un ;
■ None si φ est insatisfiable*)

let brute_force f =
    let n = max_var f in
    let v = Array.make (n + 1) false in
    try
        wh ile not (eval f v) do increment_valuation v done;
        Some v
    with
    | Last -> None


(*e fonction graph_of_cnf prenant en entrée une formule φ en 2-CNF et renvoyant
le graphe Gφ associé. On pourra supposer qu’aucune clause ne contient deux fois le même littéral, ni un
littéral et son complémenté.
*)

let graph_of_twocnf f =
    let n = max_var f in
    let g = Array.make (2 * n + 2) [] in
    let vert = function
        | P i -> 2 * i
        | N i -> 2 * i + 1 in
    let add_clause (l, l') =
        g.(vert (neg l)) <- vert l' :: g.(vert (neg l));
        g.(vert (neg l')) <- vert l :: g.(vert (neg l')) in
    List.iter add_clause f;
    g

(*fonction satisfiable déterminant si une formule φ en 2-CNF est satisfiable.
On exige une complexité linéaire en la taille de la formule (nombre d’occurrences de variables).
*)

let satisfiable f =
    let exception Unsat in
    let g = graph_of_twocnf f in
    let n = Array.length g in
    let scc_arr = Array.make n (-1) in
    let scc_list = kosaraju g in
    let assign scc_index v = scc_arr.(v) <- scc_index in
    let process_scc i scc = List.iter (assign i) scc in
    List.iteri (fun i scc -> process_scc i scc) scc_list;
    try
        for i = 0 to n / 2 - 1 do
            if scc_arr.(2 * i) = scc_arr.(2 * i + 1) then raise Unsat
        done;
    true;
    with
    | Unsat -> false

(*onction witness qui prend en entrée une formule φ dont les variables sont
x0, . . . , xn−1 et renvoie :
■ None si φ est insatisfiable ;
■ Some v, où v est un tableau de taille n codant une valuation de (x0, . . . , xn−1) satisfaisant φ, sinon*)

let witness f =
    let exception Insat in
    let g = graph_of_twocnf f in
    let n = Array.length g in
    let components = Array.of_list (kosaraju g) in
    let nb_components = Array.length components in
    let scc_of_litt = Array.make n 0 in
    for i = 0 to nb_components - 1 do
        List.iter (fun l -> scc_of_litt.(l) <- i) components.(i)
    done;
    let valuation = Array.make nb_components U in
    let neg x =
        if x mod 2 = 1 then x - 1 else x + 1 in
    let bar i =
        match components.(i) with
        | x :: _ -> scc_of_litt.(neg x)
        | [] -> failwith "empty scc: that's illegal!" in
    try
        for i = 0 to nb_components - 1 do
        match valuation.(i) with
        | U ->
            if bar i = i then raise Insat;
                valuation.(i) <- F;
                valuation.(bar i) <- T;
        | F | T -> ()
    done;
    let v = Array.make (n / 2) false in
    for i = 0 to n / 2 - 1 do
        match valuation.(scc_of_litt.(2 * i)) with
        | U -> failwith "something went very wrong :("
        | T -> v.(i) <- true
        | F -> v.(i) <- false
    done;
    Some v
    with
    | Insat -> None