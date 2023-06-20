(*on cherche a résoudre le problème de bin packing*)

type instance = int * int list

//fonction next_fit qui résout le problème en utilisant la stratégie next-fit
(*■ La stratégie next-fit considère les objets dans l’ordre d’arrivée, et ajoute ces objets dans la boîte
courante tant que c’est possible. Quand ce n’est plus le cas, on ferme (définitivement) cette boîte et
l’on en crée une nouvelle, qui devient la boîte courante.*)

let next_fit (capacity, objects) =
    let rec aux remaining_objects current_box =
        match remaining_objects with
        | [] -> [current_box]
        | x :: xs ->
        if x <= current_box.available then aux xs (add_object x current_box)
        else current_box :: aux remaining_objects (empty_box capacity) in
    aux objects (empty_box capacity)


(* fonction add_first_fit qui ajoute un objet à la première
boîte d’une liste susceptible de l’accueillir, ou crée une nouvelle boîte si aucune ne convient. Pour ce
faire, cette fonction prend aussi la capacité en argument*)

let rec add_first_fit capacity boxes x =
    match boxes with
    | [] -> [singleton capacity x]
    | b :: bs ->
    if x <= b.available then (add_object x b) :: bs
    else b :: add_first_fit capacity bs x


//fonction next_fit qui résout le problème en utilisant la stratégie first_fit*/
(*La stratégie first-fit considère aussi les objets dans l’ordre d’arrivée, mais maintient une liste (initialement vide) de boîtes B0, . . . , Bk−1. À chaque fois que l’on considère un objet, on cherche le premier
i tel que l’objet rentre dans la boîte Bi *)

let first_fit (capacity, objects) =
    let rec aux remaining_objects boxes =
        match remaining_objects with
        | [] -> boxes
        | x :: xs ->
        let boxes' = add_first_fit capacity boxes x in
        aux xs boxes' in
    aux objects []

(*idem avec la stratégie first fit decreasing
La stratégie first-fit-decreasing procède comme first-fit mais commence par trier les objets par ordre
décroissant de volume.*)

let first_fit_decreasing (capacity, objects) =
    let sorted = List.sort (fun x y -> y - x) objects in
    first_fit (capacity, sorted)


(* fonction solve calculant une solution optimale pour une instance de BinPacking. On utilisera (de manière assez basique) la technique dite Branch and Bound pour obtenir une
fonction raisonnablement efficace*)

let solve (capacity, object_list) =
    let objects = Array.of_list object_list in
    Array.sort (fun x y -> y - x) objects;
    let n = Array.length objects in
    let first_guess = first_fit_decreasing (capacity, object_list) in
    let best_boxes = ref (Array.of_list first_guess) in
    let best_k = ref (Array.length !best_boxes) in
    let boxes = Array.make !best_k (empty_box capacity) in
    let rec explore k next_object_index =
        if next_object_index = n then (
            best_k := k;
            best_boxes := Array.copy boxes
        ) else if k < !best_k then (
            let x = objects.(next_object_index) in
            for i = 0 to k - 1 do
            if x <= boxes.(i).available then (
                let b = boxes.(i) in
                boxes.(i) <- add_object x b;
                explore k (next_object_index + 1);
                boxes.(i) <- b
        )
        done;
        if k < !best_k - 1 then (
            boxes.(k) <- singleton capacity x;
            explore (k + 1) (next_object_index + 1);
            boxes.(k) <- empty_box capacity
            )
        ) in
    explore 0 0;
    Array.to_list (Array.sub !best_boxes 0 !best_k)


