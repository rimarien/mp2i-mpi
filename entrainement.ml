(*fonction binom (k : int) (n : int) : int qui calcule (n
k
) en utilisant la for-
mule du triangle de Pascal. On rappelle que (n
k
) vaut 0 sauf si 0 6 k 6 n.*)

let rec binom k n =
	if k < 0 || k > n then 0
	else if k = 0 || k = n then 1
	else binom k (n - 1) + binom (k - 1) (n - 1)
	
(*fonction triangle : int -> int array array prenant en entrée un entier n
supposé positif ou nul et renvoyant un tableau t tel que :
 t est de longueur n + 1 ;
 pour 0 6 i 6 n, t.(i) est de longueur i + 1 ;
 pour 0 6 j 6 i 6 n, t.(i).(j) vaut (i
j
).*)

let triangle n =
	let t = Array.make (n + 1) [| |] in
	for i = 0 to n do
		t.(i) <- Array.make (i + 1) 1;
		for j = 1 to i - 1 do
			t.(i).(j) <- t.(i - 1).(j) + t.(i - 1).(j - 1)
		done
	done;
	t
	
(* fonction binom_it : int -> int -> int calculant (n
k
).*)

let binom_it k n =
	if k < 0 || k > n then 0
	else (triangle n).(n).(k)
	
let rec fact n =
	if n = 0 then 1
	else n * fact (n - 1)
	
(*fonction
binom_formule : int -> int -> int effectuant le calcul d’un coefficient binomial en
temps linéaire en n.*)

let binom_formule k n =
	if k < 0 || k > n then 0
	else (fact n) / (fact k * fact (n - k))
	
(* fonction calculant (n
k
) en temps linéaire et n’ayant pas le problème
de binom_formule*) 

let rec binom_eff k n =
	if k < 0 || k > n then 0
	else if k = 0 then 1
	else n * binom_eff (k - 1) (n - 1) / k
	
(* fonction cherche_naif : int -> int array array -> bool résolvant le pro-
blème de la manière la plus simple possible*)

(*fonction couvertures : int list -> int -> int telle que couverture u n ren-
voie le nombre de manières de couvrir une ligne de n cases avec des tuiles de longueurs
données par u. Par exemple, si u = [1; 3; 1] il y a trois types de tuiles, dont deux sont de
longueur 1 et un de longueur 3. On demande une solution concise, sans trop se soucier de
l’efficacité*)