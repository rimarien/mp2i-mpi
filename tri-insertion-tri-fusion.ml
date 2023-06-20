(*recherche de l'élément x dans le tableau t de façon dichotomique*)

let cherche_dicho t x =
    let rec aux deb fin =
        if deb >= fin then None
        else
            let mil = (deb + fin) / 2 in
            if t.(mil) = x then Some mil
            else if t.(mil) < x then aux (mil + 1) fin
            else aux deb mil in
    aux 0 (Array.length t)
	
(* fonction insere prenant en entrée une liste v supposée triée par ordre croissant
et un élément x, et renvoyant une nouvelle version de v dans laquelle x a été inséré à la
bonne place (pour que la liste reste croissante)*)

let rec insere m x =
    match m with
    | [] -> [x]
    | y :: ys when x <= y -> x :: m
    | y :: ys -> y :: (insere ys x)
	
(*Entrée : une liste u (dont les éléments sont comparables).
Sortie : une liste v telle que sorted(u) = v*)

let rec tri_insertion m =
    match m with
    | [] -> []
    | x :: xs -> insere (tri_insertion xs) x
	
(*fonction échange telle que echange t i j
échange les élémets d’indice i et j du tableau t*)

let echange t i j =
    let x = t.(i) in
    t.(i) <- t.(j);
    t.(j) <- x
	
(* fonction insertion_en_place : 'a array -> int -> unit ayant la spécifica-
tion suivante :
Entrées : un tableau t et un entier i.
Préconditions :
 0 < i < |t|
 isSorted(t[: i])
Effets secondaires : après l’appel, on a en notant tinit l’état initial (avant l’appel) de t :
 ms(t[: i + 1]) = ms(tinit[: i + 1])
 isSorted(t[: i + 1])
 t[i + 1 :] = tinit[i + 1 :*)

let insertion_en_place t i =
    let j = ref i in
    while !j > 0 && t.(!j) < t.(!j - 1) do
        echange t !j (!j - 1);
        decr j
    done
	
let tri_insertion_tableau t =
    for i = 1 to Array.length t - 1 do
    insertion_en_place t i
    done
	
let insertion_en_place_bis t i =
    let j = ref i in
    let x = t.(i) in
    while !j > 0 && t.(!j - 1) > x do
        t.(!j) <- t.(!j - 1);
        decr j
    done;
    t.(!j) <- x
	
(*fonction eclate : 'a list -> ('a list * 'a list) telle que l’appel
eclate u renvoie un couple (ga, dr) vérifiant :
 0 6 |ga| − |dr| 6 1
 ms(ga + dr) = ms(u)
*)

let rec eclate u =
    match u with
    | [] -> ([], [])
    | [x] -> ([x], [])
    | x :: y :: reste -> let a, b = eclate reste in (x :: a, y :: b)
	
(*fonction fusionne : 'a list -> 'a list -> 'a list décrite plus haut. Sa spé-
cification précise est :
Entrées : deux listes u et v.
Précondition : isSorted(u) et isSorted(v).
Sortie : une liste w telle que w = sorted(u + v) *)

let rec tri_fusion u =
    match u with
    | [] | [_] -> u
    | _ -> let (a, b) = eclate u in
    fusionne (tri_fusion a) (tri_fusion b)

(*fonction nb_occs_trie : 'a -> 'a array -> int telle que nb_occs_trie x t cal-
cule efficacement |t|x en supposant que le tableau t est trié *)

let premiere_occ t x =
    let n = Array.length t in
    let rec aux deb fin =
        if deb >= fin then n
        else
            let mil = (deb + fin) / 2 in
            if t.(mil) = x then min mil (aux deb mil)
            else if t.(mil) < x then aux (mil + 1) fin
            else aux deb mil in
    aux 0 n
    
let derniere_occ t x =
    let n = Array.length t in
    let rec aux deb fin =
        if deb >= fin then -1
        else
            let mil = (deb + fin) / 2 in
            if t.(mil) = x then max mil (aux (mil + 1) fin)
            else if t.(mil) < x then aux (mil + 1) fin
            else aux deb mil in
    aux 0 n
	
let nb_occs_triee t x =
    let premiere = premiere_occ t x in
    let derniere = derniere_occ t x in
    max 0 (derniere - premiere + 1)