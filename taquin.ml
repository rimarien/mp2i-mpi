type state = {
    grid : int array array;
    mutable i : int;
    mutable j : int;
    mutable h : int;
}

type direction = U | D | L | R | No_move

let delta = function
    | U -> (-1, 0)
    | D -> (1, 0)
    | L -> (0, -1)
    | R -> (0, 1)
    | No_move -> assert false

(*fonction possible_moves qui renvoie la liste des directions de déplacement
légales à partir d’un certain état.
*)

let possible_moves state =
    let possible = ref [] in
    if state.i > 0 then possible := U :: !possible;
    if state.i < n - 1 then possible := D :: !possible;
    if state.j > 0 then possible := L :: !possible;
    if state.j < n - 1 then possible := R :: !possible;
    !possible

(*fonction compute_h qui prend en entrée un état, dans lequel le champ h a une
valeur quelconque, et donne à ce champ la bonne valeur*)

let compute_h state =
    let h = ref 0 in
    for i = 0 to n - 1 do
        for j = 0 to n - 1 do
            if i <> state.i || j <> state.j then
                h := !h + distance i j state.grid.(i).(j)
        done
    done;
    state.h <- !h

(* fonction delta_h qui prend en entrée un état e et une direction d et renvoie la
différence h(e') − h(e), où e est l’état que l’on atteint à partir de e en effectuant le déplacement d. On ne
fera que les calculs nécessaires (on évitera donc de recalculer toute la somme définissant h)*)

let delta_h state move =
    let (di, dj) = delta move in
    let i = state.i in
    let j = state.j in
    let x = state.grid.(i + di).(j + dj) in
    distance i j x - distance (i + di) (j + dj) x

(*e fonction apply qui modifie un état en lui appliquant un déplacement, que l’on
supposera légal*)

let apply state move =
    let i = state.i in
    let j = state.j in
    let (di, dj) = delta move in
    let x = state.grid.(i + di).(j + dj) in
    state.h <- state.h + delta_h state move;
    state.grid.(i).(j) <- x;
    state.i <- i + di;
    state.j <- j + dj

(* fonction copy qui prend un état et en renvoie une copie. On pourra utiliser la
fonction Array.copy, mais attention : grid est un tableau de tableaux... *)

let copy state =
    {grid = Array.init n (fun i -> Array.copy state.grid.(i));
    i = state.i;
    j = state.j;
    h = state.h}

(* fonction successors qui prend en entrée un état et renvoie la liste de ses
successeurs dans le graphe (ou de ses voisins, d’ailleurs, le graphe n’étant pas orienté).
*)

let successors state =
    let rec aux moves =
    match moves with
    | [] -> []
    | m :: ms ->
        let s = copy state in
        apply s m;
        s :: aux ms in
    aux (possible_moves state)

(*fonction reconstruct
qui prend en entrée un dictionnaire codant un arbre et un nœud x de l’arbre, et renvoie un chemin de la
racine à x, sous la forme d’une liste de nœuds.*)

let reconstruct parents x =
    let rec aux v path =
        let p = Hashtbl.find parents v in
        if p = v then v :: path
        else aux p (v :: path) in
    aux x []



exception No_path


(*fonction astar prenant en entrée un état initial et calculant un chemin de
longueur minimale vers l’état final à l’aide de l’algorithme A⋆
. Cette fonction lèvera l’exception No_path
si aucun chemin n’existe.*)

let astar initial =
    let dist = Hashtbl.create 100 in
    let parents = Hashtbl.create 100 in
    Hashtbl.add parents initial initial;
    let q = Heap.create () in
    Heap.insert q (initial, initial.h);
    Hashtbl.add dist initial 0;
    let rec loop () =
        match Heap.extract_min q with
        | None -> raise No_path
        | Some (x, _) when x.h = 0 -> reconstruct parents x
        | Some (x, _) ->
        let dx = Hashtbl.find dist x in
        let process v =
            let dv = dx + 1 in
            match Hashtbl.find_opt dist v with
            | Some d when d <= dv -> ()
            | _ ->
                Hashtbl.replace dist v dv;
            Heap.insert_or_decrease q (v, dv + v.h);
            Hashtbl.replace parents v x in
        List.iter process (successors x);
        loop () in
    loop ()



let opposite = function
| L -> R
| R -> L
| U -> D
| D -> U
| No_move -> No_move

let idastar_length initial =
    let exception Found of int in
    let state = copy initial in
    let rec search depth bound =
        if depth + state.h > bound then depth + state.h
        else if state.h = 0 then raise (Found depth)
        else
            let minimum = ref max_int in
            let make_move direction =
                apply state direction;
                minimum := min !minimum (search (depth + 1) bound);
                apply state (opposite direction); in
            List.iter make_move (possible_moves state);
            !minimum in
    let rec loop bound =
        let m = search 0 bound in
        if m = max_int then None
        else loop m in
    try
        loop state.h
    with
    | Found depth -> Some depth




let idastar initial =
    let counter = ref 0 in
    let state = copy initial in
    let exception Found in
    let path = Vector.create () in
    let rec search depth bound last_move =
        incr counter;
        if depth + state.h > bound then depth + state.h
        else if state.h = 0 then raise Found
        else
            let minimum = ref max_int in
            let make_move direction =
                if direction <> opposite last_move then (
                    Vector.push path direction;
                    apply state direction;
                    minimum := min !minimum (search (depth + 1) bound direction);
                    apply state (opposite direction);
                    ignore (Vector.pop path)
                ) in
            List.iter make_move (possible_moves state);
            !minimum in
    let rec loop bound =
        let m = search 0 bound No_move in
        if m = max_int then None
        else loop m in
    try
        loop state.h
    with
    | Found ->
    Printf.printf "%d node expansions\n" !counter;
    Some path