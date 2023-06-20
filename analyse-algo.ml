let rec fib_naif n =
	if n <= 1 then n
	else fib_naif (n - 1) + fib_naif (n - 2)
	
(* fonction fib_iter : int -> int calculant Fn en temps O(n). On utilisera une
boucle et des référence*)

let fib_iter n =
	let f1 = ref 0 in
	let f2 = ref 1 in
	(* invariant f1 = F_i, f2 = F_{i + 1} *)
	for i = 0 to n - 1 do
		let tmp = !f1 in
		f1 := !f2;
		f2 := !f2 + tmp
	done;
	(* i = n (conceptuellement) en sortie de boucle,
	* donc f1 = F_n *)
	!f1

(*fonction fib_rec : int -> int faisant la même chose (avec la même com-
plexité) mais n’utilisant ni boucles ni référence*)

let fib_rec n =
	let rec aux i f1 f2 =
		if i = n then f1 else aux (i + 1) f2 (f1 + f2) in
	aux 0 0 1

(*fonction tri_decroissant : int list -> int list triant son argument en ordre
décroissant *)

let tri_decroissant u = List.sort (fun x y -> y - x) u
(* ou plus simplement *)
let tri_decroissant = List.sort (fun x y -> y - x)

(* fonction tri_valeur_absolue : float list -> float list triant son argument par
valeur absolue croissante*)

let compare_abs x y =
	let diff = abs_float x -. abs_float y in
	if diff < 0. then -1
	else if diff > 0. then 1
	else 0
	
let tri_valeur_absolue = List.sort compare_abs

(*fonction tri_deuxieme_composante : ('a * int) list -> ('a * int) list triant
son argument par deuxième composante croissante*)

let compare_deuxieme (_, y) (_, y') = y - y'

let tri_deuxieme_composante = List.sort compare_deuxieme

(* fonction records : (cmp : 'a -> 'a -> int) -> (u : 'a list) -> 'a list qui
renvoie la liste des « records » de u, c’est-à-dire des éléments de u qui sont strictement plus
grands que tous ceux qui les précèdent, au sens de la fonction de comparaison cmp fournie*)

let rec records cmp u =
	match u with
	| [] -> []
	| [x] -> [x]
	| x :: y :: xs ->
		if cmp x y < 0 then x :: records cmp (y :: xs)
		else records cmp (x :: xs)
		
(*’algorithme d’Euclide pour calculer le PGCD de deux entiers naturels*)	
let rec pgcd a b =
	if b = 0 then a else pgcd b (a mod b)

(*On note f(a, b) le nombre de divisions (opérations mod) effectuées par la fonction pgcd lorsqu’elle est
appelée sur a et b.
fonction etapes : int -> int -> int qui calcule le f défini plus haut*)

let rec etapes a b =
	if b = 0 then 0 else 1 + etapes b (a mod b)

(*On définit la fonction φ pour n ∈ N∗ par φ(n) = max
06k<n f(n, k).
 fonction phi : int -> int spécifiée ci-dessus*)
 
 
let phi n =
	let rec max_liste = function
		| [] -> failwith "max d'une liste vide"
		| [x] -> x
		| x :: xs -> max x (max_liste xs) in
	(* liste_etapes = [etapes n 0; etapes n 1; ...; etapes n (n - 1)] *)
	let liste_etapes = List.init n (etapes n) in
	max_liste liste_etapes
	
(* fonction records_euclide (borne : int) -> (int * int) list qui ren-
voie la liste des couples (n, φ(n)) avec 1 6 n < borne et φ(n) « record » (c’est-à-dire
plus grand que tous les φ(k) avec k < n).*)
	
let records_euclide borne =
	(* liste_couples = [(1, phi 1); (2, phi 2); ...; (borne, phi borne)] *)
	let liste_couples = List.init borne (fun n -> (n + 1, phi (n + 1))) in
	let cmp (n, phi_n) (n', phi_n') = phi_n - phi_n' in
	records cmp liste_couples
	
let records_f n =
	let liste_couples = List.init n (fun i -> (i + 1, f (i + 1))) in
	let cmp (_, fi) (_, fi') = fi - fi' in
	records cmp liste_couples