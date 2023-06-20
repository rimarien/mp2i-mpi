type 'a file_fonct = 'a list * 'a list

(* Une constante égale à la file ne contenant aucun élément. *)
let file_vide = ([], [])

(*fonction miroir : 'a list -> 'a list se comportant comme List.rev. On
exige une complexité linéaire en la taille de la liste.*)
let miroir u = 
  let rec aux u v = 
    match u with
      | [] -> v
      | x :: xs -> aux xs (x :: v) in
  aux u []
  
(* ajoute x f renvoie une nouvelle file contenant les éléments de f, plus x *)
let ajoute x (u, v) = (x :: u, v)

(* enleve f renvoie Some (x, f'), où x est l'élément le plus ancien
de f et f' est la file obtenue en enlevant x à f.
Si f est vide, on renverra None. *)
let rec enleve f =
  match f with
  | u, x :: xs -> Some (x, (u, xs))
  | [], [] -> None
  | u, [] -> enleve ([], miroir u)
 
 
(*fonction somme : int file_fonct -> int renvoyant la somme des éléments
d’une file*)

 let rec somme f =
  match enleve f with
  | None -> 0
  | Some (x, f') -> x + somme f'

(*fonction file_fonct_of_list : 'a list -> 'a file_fonct qui convertit une
liste en file, l’élément de tête de la liste se retrouvant « à droite » de la file*)

let file_fonct_of_list u =
  let rec aux u f =
    match u with
    | [] -> f
    | x :: xs -> aux xs (ajoute x f) in
  aux u file_vide
 
let file_fonct_of_list_2 u = ([], u)

(*onction itere_file : ('a -> unit) -> 'a file_fonct -> unit telle que
l’appel itere_file f file, où file = (x1, . . . , xn) (avec xn le plus ancien élément), soit
équivalent à appeler la fonction f successivement sur xn, puis xn−1, . . . , puis x1*)

let rec itere_file f file =
  match enleve file with
  | None -> ()
  | Some (x, xs) -> f x ; itere_file f xs
  
(*fonction afficher : int file_fonct -> unit qui affiche tous les éléments
d’une file d’entiers, dans leur ordre d’insertion. On rappelle que :
 print_int : int -> unit permet d’afficher un entier ;
 print_newline : unit -> unit permet de revenir à la ligne.*)

 let affiche file =
  let f n = print_int n; print_newline () in
  itere f file
  
type 'a pile = {donnees : 'a option array; mutable courant : int}

let capacite p = Array.length p.donnees

let nouvelle_pile n = 
  {donnees = Array.make n None; courant = -1}
  
let pop s = 
  if s.courant = -1 then 
    None 
  else 
    begin
      let x = s.donnees.(s.courant) in 
      s.courant <- s.courant - 1;
      x
    end

let push x s =
  if s.courant >= capacite s - 1 then
    failwith "Pile pleine"
  else
    begin
      s.courant <- s.courant + 1;
      s.donnees.(s.courant) <- Some x
    end

type 'a file_i =
  {donnees : 'a option array;
   mutable entree : int;
   mutable sortie : int;
   mutable cardinal : int}
  
(*file_vide_i : int -> 'a file_i où l’entier spécifie la capacité de la file*)

let file_vide_i n =
  {donnees = Array.make n None;
   entree = 0;
   sortie = 0;
   cardinal = 0}
 
(*capacite_i : 'a file_i -> int qui renvoie la capacité *) 

let capacite_i f = Array.length f.donnees

(*ajoute_i : 'a -> 'a file_i -> unit (si la file est pleine, on le signalera en levant une
exception par failwith "Insertion dans file pleine")*)

let ajoute_i x f =
  let n = capacite_i f in
  if f.cardinal = n then failwith "file pleine";
  let t = f.donnees in
  t.(f.entree) <- Some x;
  f.entree <- (f.entree + 1) mod n;
  f.cardinal <- f.cardinal + 1
  
(*enleve_i : 'a file_i -> 'a option (on modifiera la file, et renverra None si elle est déjà
vide) *)

let enleve_i f =
  if f.cardinal = 0 then None
  else begin
      let t = f.donnees in
      let x = t.(f.sortie) in
      f.sortie <- (f.sortie + 1) mod (capacite_i f);
      f.cardinal <- f.cardinal - 1;
      x
    end

(*de_liste_i : 'a list -> int -> 'a file_i. On demande que de_liste_i u n crée une
file de capacité n et y ajoute les éléments de u en commençant par l’élément de tête. On
pourra supposer sans le vérifier que n > |u*)

let de_liste_i u n =
  let f = file_vide_i n in
  let rec aux = function
    | [] -> ()
    | x :: xs -> ajoute_i x f; aux xs in
  aux u;
  f

(* fonction peek_1 : 'a pile -> 'a option, qui renvoie Some x si on l’appelle
sur une pile de sommet x, None si on l’appelle sur une pile vide. Cette fonction ne doit pas
modifier son argument*)

let peek_1 s =
  match pop s with
  | None -> None
  | Some x -> push x s; Some x

(* fonction est_vide_1 : 'a pile -> bool qui détermine si son argument est
vide*)

let est_vide_1 s =
  peek_1 s = None

(* fonction iter_destructif : (f : 'a -> unit) -> (s : 'a pile) -> unit
qui applique la fonction f successivement à chacun des éléments de s en commençant par
le sommet. À la fin de l’appel, s sera vide*)

let rec iter_destructif f s =
  match pop s with
  | None -> ()
  | Some x -> f x; iter_destructif f s
  
let copie s =
  let s_copie = nouvelle_pile (capacite s) in
  let miroir = nouvelle_pile (capacite s) in
  iter_destructif (fun x -> push x miroir) s;
  iter_destructif (fun x -> push x s_copie; push x s) miroir;
  s_copie
  
let egal s t =
  egal_destructif (copie s) (copie t)
  
(* est_vide : 'a pile -> bool*)
  
let est_vide s =
  s.courant = -1

(*Fonction flush : 'a pile -> unit qui vide son argument (sans rien faire avec ses élé-
ments) ; on attend une implémentation en temps constant.*)

let flush s =
  s.courant <- -1
  
(*Fonction egal : 'a pile -> 'a pile -> bool (attention, il faut bien tester l’égalité des
éléments des piles, ce qui n’est pas la même chose que l’égalité des contenus des tableaux).*)

let egal_bis s t =
  if s.courant != t.courant then false
  else
    begin
      let k = ref 0 in
      while !k <= s.courant && s.donnees.(!k) = t.donnees.(!k) do
        incr k
      done;
      !k = s.courant + 1
    end

(*Fonction itere : ('a -> unit) -> 'a pile -> unit, version non destructive de
iter_destructif*)

let itere f pile =
  for i = pile.courant downto 0 do
    match pile.donnees.(i) with
    | None -> failwith "impossible"
    | Some x -> f x
  done
  



