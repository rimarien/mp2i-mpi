open Printf

type coup = int
type direction = int * int

let nb_lignes = 6
let nb_colonnes = 7


type position = {
  grille : float array array;
  hauteurs : int array;
  mutable dernier : int;
  mutable nb_joues : int;
  mutable code : int;
}

let creer_initiale () = {
  grille = Array.make_matrix nb_lignes nb_colonnes 0.;
  hauteurs = Array.make nb_colonnes 0;
  nb_joues = 0;
  dernier = -1;
  code = 0;
}

let affiche position =
  let open Printf in
  let bordure = String.make (nb_colonnes + 2) '_' in
  printf " ";
  print_endline bordure;
  for ligne = nb_lignes - 1 downto 0 do
    printf "%d|" ligne;
    for col = 0 to nb_colonnes - 1 do
      let x = position.grille.(ligne).(col) in
      if x = 1. then printf "X"
      else if x = -1. then printf "O"
      else printf " "
    done;
    printf "|\n"
  done;
  printf " ";
  print_endline (String.make (nb_colonnes + 2) '-');
  printf "  ";
  for col = 0 to nb_colonnes - 1 do printf "%d" col done;
  print_newline ()

let joueur_courant position =
  if position.nb_joues mod 2 = 0 then 1.
  else -1.


let en_jeu i j =
  0 <= i && i < nb_lignes && 0 <= j && j < nb_colonnes

let compte_consecutifs position ligne col (di, dj) =
  let nb = ref 0 in
  let g = position.grille in
  let joueur = g.(ligne).(col) in
  let i = ref ligne in
  let j = ref col in
  while en_jeu !i !j && g.(!i).(!j) = joueur do
    incr nb;
    i := !i + di;
    j := !j + dj
  done;
  i := ligne - di;
  j := col - dj;
  while en_jeu !i !j && g.(!i).(!j) = joueur do
    incr nb;
    i := !i - di;
    j := !j - dj
  done;
  !nb

let tab_valeurs =
  [|
    [| 3.; 4.; 5.; 7.; 5.; 4.; 3.|];
    [| 4.; 6.; 7.; 10.; 7.; 6.; 4.|];
    [| 5.; 8.; 11.; 13.; 11.; 8.; 5.|];
    [| 5.; 8.; 11.; 13.; 11.; 8.; 5.|];
    [| 4.; 6.; 7.; 10.; 7.; 6.; 4.|];
    [| 3.; 4.; 5.; 7.; 5.; 4.; 3.|];
  |]


(*fonction coups_possibles prenant en entrée une positon et renvoyant la liste
des coups (numéros de colonne) légaux.*)

let coups_possibles position =
    let rec aux c =
        if c = nb_colonnes then []
        else if position.hauteurs.(c) < nb_lignes then c :: aux (c + 1)
        else aux (c + 1) in
    aux 0

(* fonction joue prenant en entrée une position et un coup, et modifiant la position
en jouant ce coup.*)

let joue position col =
    let ligne = position.hauteurs.(col) in
    let joueur = joueur_courant position in
    assert (ligne < nb_lignes && position.nb_joues < nb_lignes * nb_colonnes);
    position.grille.(ligne).(col) <- joueur;
    position.hauteurs.(col) <- ligne + 1;
    position.dernier <- col;
    position.nb_joues <- position.nb_joues + 1

(* fonction restore prenant en entrée une position et l’avant-dernier coup joué, et
annulant le dernier coup joué.*)

let restore position ancienne_col =
    let col = position.dernier in
    let ligne = position.hauteurs.(col) in
    position.grille.(ligne - 1).(col) <- 0.;
    position.hauteurs.(col) <- ligne - 1;
    position.dernier <- ancienne_col;
    position.nb_joues <- position.nb_joues - 1

(* fonction perdant prenant en entrée une position et renvoyant true si et seulement
si le dernier coup joué a créé un alignement d’au moins 4 jetons (et donc si la position est
perdante pour le joueur qui devrait jouer à présent)*)

let perdant position =
    let col = position.dernier in
    if col = -1 then false
    else
        let ligne = position.hauteurs.(col) - 1 in
        let f (di, dj) = compte_consecutifs position ligne col (di, dj) in
        f (0, 1) >= 4 || f (1, 0) >= 4 || f (1, 1) >= 4 || f (1, -1) >= 4

type strategie : position -> coup

(*stratégie strat_alea choisissant systématiquement un coup (légal) au hasard*)

let strat_alea position =
    let possibles = Array.of_list (coups_possibles position) in
    possibles.(Random.int (Array.length possibles))

(*e fonction joue_partie prenant en entrée deux stratégies et les faisant jouer l’une
contre l’autre (celle passée en premier argument joue en premier). On affichera l’état du
plateau à chaque étape*)

let joue_partie strat1 strat2 =
    let position = creer_initiale () in
    let rec aux s1 s2 =
    let coup = s1 position in
        joue position coup;
        affiche position;
        if perdant position then -. joueur_courant position
        else if position.nb_joues = nb_lignes * nb_colonnes then 0.
        else aux s2 s1 in
    affiche position;
    aux strat1 strat2


(*stratégie strat_humain faisant jouer un humain*)

let strat_humain positon =
    printf "colonne ?\n";
    let c = read_int () in
    c

(*fonction heuristique_basique prenant en entrée une position et renvoyant la
valeur correspondante de l’heuristique *)

let heuristique_basique position =
    let s = ref 0. in
    for l = 0 to nb_lignes - 1 do
        for c = 0 to nb_colonnes - 1 do
            s := !s +. position.grille.(l).(c) *. tab_valeurs.(l).(c)
        done
    done;
    !s
    
(* fonction negamax prenant en entrée :
■ une fonction heuristique : position -> float;
■ une profondeur d’exploration pmax (en demi-coups) ;
■ une position pos.
et renvoyant un couple (c, v) où v est l’évaluation de la position par une exploration à
profondeur pmax et c est le coup à jouer. Une position déterminée comme gagnante sera
évaluée à infinity, et une positon perdante à neg_infinity.*)

let rec negamax h position profondeur =
    let joueur = joueur_courant position in
    if perdant position then (-1, neg_infinity)
    else if position.nb_joues = nb_lignes * nb_colonnes then (-1, 0.)
    else if profondeur = 0 then (-1, joueur *. h position)
    else
        let rec aux possibles coup_max eval_max =
            match possibles with
            | [] -> (coup_max, eval_max)
            | coup :: autres ->
            let dernier = position.dernier in
            joue position coup;
            let (_, x) = negamax h position (profondeur - 1) in
            let eval = -. x in
            restore position dernier;
            if eval = infinity then (coup, infinity)
            else if eval >= eval_max then aux autres coup eval
            else aux autres coup_max eval_max in
        aux (coups_possibles position) (-1) neg_infinity

let strat_nega prof position =
    let (coup, eval) = negamax heuristique_basique position prof in
    printf "\neval negamax profondeur %d : %f\n" prof eval;
    coup

(* fonction alphabeta prenant en entrée :
■ une fonction heuristique : position -> float;
■ une profondeur d’exploration pmax (en demi-coups) ;
■ une position pos;
■ deux flottants α et β
et renvoyant un couple (c, v) tel que :
■ si l’évaluation négamax de la position à la profondeur donnée est comprise entre α et
β, alors v est égal à cette évaluation et c est le coup correspondant ;
■ si l’évaluation négamax est inférieure ou égale à α, alors v est inférieur ou égal à α;
■ si elle est supérieure ou égale à β, alors v est supérieur ou égal à β.
Cette fonction procédera par élagage αβ*)

let rec alphabeta h position profondeur alpha beta =
    let joueur = joueur_courant position in
    if perdant position then (-1, neg_infinity)
    else if position.nb_joues = nb_lignes * nb_colonnes then (-1, 0.)
    else if profondeur = 0 then (-1, joueur *. h position)
    else
        let rec aux possibles coup_max eval_max =
            match possibles with
            | [] -> (coup_max, eval_max)
            | coup :: autres ->
            let dernier = position.dernier in
            joue position coup;
            let (_, x) = alphabeta h position (profondeur - 1)
                (-.beta) (-. eval_max) in
            let eval = -. x in
            restore position dernier;
            if eval >= beta then (coup, eval)
            else if eval > eval_max then aux autres coup eval
            else aux autres coup_max eval_max in
    let possibles = coups_possibles position in
    aux possibles (List.hd possibles) alpha

type code = int

let largeur_colonne = 9
let masque_colonne = 1 lsl largeur_colonne - 1


(*fonction extrait_colonne telle que l’appel extrait_colonne x j renvoie l’entier (sur 9 bits) correspondant à la colonne d’indice j*)
let extrait_colonne x j =
(x lsr (j * largeur_colonne)) land masque_colonne

(* fonction remplace_colonne telle que l’appel
remplace_colonne x j valeur_colonne remplace les 9 bits de x codant la colonne
j par valeur_colonne.
*)

let remplace_colonne x j valeur_colonne =
    let masque = lnot (masque_colonne lsl (j * largeur_colonne)) in
    let x' = x land masque in
    x' lor (valeur_colonne lsl (j * largeur_colonne))

(* fonction ajoute_colonne qui prend en entrée l’entier sur 9 bits codant une
colonne et un flottant codant le joueur, et renvoie l’entier codant la colonne dans laquelle
on a ajouté (au sommet) un jeton du joueur précisé*)

let ajoute_colonne valeur_colonne joueur =
    let h = valeur_colonne land 0b111 in
    let cases = valeur_colonne lsr 3 in
    let cases' =
        if joueur = 1. then cases lor (1 lsl h)
        else cases in
    (cases' lsl 3) + (h + 1)

(* fonction enleve_colonne prenant en entrée l’entier codant une colonne et renvoyant l’entier codant la colonne dans laquelle le jeton au sommet a été supprimé*)

let enleve_colonne valeur_colonne =
    let h = valeur_colonne land 0b111 in
    let cases = valeur_colonne lsr 3 in
    let cases' = cases land (lnot (1 lsl (h - 1))) in
    (cases' lsl 3) + (h - 1)

(* fonction joue_code tel que l’appel joue_code x j joueur renvoie le code x
obtenu à partir de x en faisant joueur le joueur joueur dans la colonne d’indice j*)

let joue_code x j joueur =
    let col = extrait_colonne x j in
    let col' = ajoute_colonne col joueur in
    remplace_colonne x j col'

(* fonction annule_code tel que l’appel annule_code x j renvoie le code x obtenu
à partir de x en supprimant le jeton au sommet de la colonne d’indice j*)

let annule_code x j =
    let col = extrait_colonne x j in
    let col' = enleve_colonne col in
    remplace_colonne x j col'

(*x fonctions joue_avec_code et restore_avec_code similaires aux fonctions joue
et restore codées précédemment mais mettant également à jour le code de la position.*)

let joue_avec_code position col =
    let ligne = position.hauteurs.(col) in
    let joueur = joueur_courant position in
    assert (ligne < nb_lignes && position.nb_joues < nb_lignes * nb_colonnes);
    position.grille.(ligne).(col) <- joueur;
    position.hauteurs.(col) <- ligne + 1;
    position.dernier <- col;
    position.nb_joues <- position.nb_joues + 1;
    position.code <- joue_code position.code col joueur

let restore_avec_code position ancienne_col =
    let col = position.dernier in
    let ligne = position.hauteurs.(col) in
    position.grille.(ligne - 1).(col) <- 0.;
    position.hauteurs.(col) <- ligne - 1;
    position.dernier <- ancienne_col;
    position.nb_joues <- position.nb_joues - 1;
    position.code <- annule_code position.code col

(*fonction alphabeta_transpo se comportant comme la fonction alphabeta mais
prenant (et utilisant!) un argument supplémentaire de type (code, float) Hashtbl.t
correspondant à la table de transposition.*)

let rec alphabeta_transpo table h position profondeur alpha beta =
    match Hashtbl.find_opt table position.code with
    | Some (coup, valeur) ->
    (coup, valeur)
    | _ ->
        let coup, valeur =
            let joueur = joueur_courant position in
            if perdant position then (-1, neg_infinity)
            else if position.nb_joues = nb_lignes * nb_colonnes then (-1, 0.)
            else if profondeur = 0 then (-1, joueur *. h position)
            else
                let rec aux possibles coup_max eval_max =
                    match possibles with
                    | [] -> (coup_max, eval_max)
                    | coup :: autres ->
                        let dernier = position.dernier in
                        joue_avec_code position coup;
                        let (_, x) =
                            alphabeta_transpo
                            table h position (profondeur - 1)
                            (-.beta) (-. eval_max) in
                        let eval = -. x in
                        restore_avec_code position dernier;
                        if eval >= beta then (coup, eval)
                        else if eval > eval_max then aux autres coup eval
                        else aux autres coup_max eval_max in
                    let possibles = coups_possibles position in
                    aux possibles (List.hd possibles) alpha in
                if abs_float valeur = infinity
                    || (alpha < valeur && valeur < beta) then
                        Hashtbl.add table position.code (coup, valeur);
            (coup, valeur)



let strat_alphabeta_2 prof position =
    let t = Hashtbl.create 100_000 in
    let (coup, x) =
        alphabeta_transpo
            t heuristique_basique position prof neg_infinity infinity in
    let symbole = if joueur_courant position = 1. then 'X' else 'O' in
    printf "\n\neval alphabeta_2 %c: %f\n" symbole x;
    coup

let main () =
  Printexc.record_backtrace true;
  printf "à écrire\n"

(* let () = main () *)
