type etat = int
type lettre = int
type mot = lettre list

type afd =
  {m : int;
   n : int;
   init : etat;
   term : bool array;
   delta : etat array array}

type description =
  {initial : etat;
   acceptants : etat list;
   transitions : (etat * lettre * etat) list}

let description_a1 =
  {initial = 0;
   acceptants = [2];
   transitions = [(0, 0, 2); (0, 1, 0);
                  (1, 0, 0); (1, 2, 2);
                  (2, 0, 2); (2, 2, 1)]}


let construit d =
  let rec aux = function
    | [] -> min_int, min_int
    | (q, x, q') :: v -> let maxq, maxx = aux v in
      (max maxq (max q q'), max maxx x) in
  let etat_max, lettre_max = aux d.transitions in
  let n = etat_max + 1 in
  let m = lettre_max + 1 in
  let term = Array.make n false in
  let delta = Array.make_matrix n m (-1) in
  List.iter (fun i -> term.(i) <- true) d.acceptants;
  List.iter (fun (q, x, q') -> delta.(q).(x) <- q') d.transitions;
  {n = n;
   m = m;
   term = term;
   init = d.initial;
   delta = delta}


let graphviz a ?etats:(etats=[||]) ?lettres:(lettres=[||]) filename =
  let open Printf in
  let out = open_out filename in
  fprintf out "digraph a {\nrankdir = LR;\n";
  (* noms des états *)
  let nom_etat =
    if etats = [||] then string_of_int
    else (fun i -> etats.(i)) in
  (* noms des lettres *)
  let nom_lettre =
    if lettres = [||] then string_of_int
    else (fun i -> lettres.(i)) in
  (* etats *)
  for q = 0 to a.n - 1 do
    let shape = if a.term.(q) then "doublecircle" else "circle" in
    fprintf out "node [shape = %s, label = %s] %i;\n" shape (nom_etat q) q
  done;
  (* etat initial *)
  fprintf out "node [shape = point]; I\n";
  fprintf out "I -> %i;\n" a.init;
  (* transitions *)
  let labels = Array.make_matrix a.n a.n [] in
  for q = 0 to a.n - 1 do
    for x = a.m - 1 downto 0 do
      let q' = a.delta.(q).(x) in
      if q' <> -1 then
        labels.(q).(q') <- nom_lettre x :: labels.(q).(q')
    done
  done;
  for q = 0 to a.n - 1 do
    for q' = 0 to a.n - 1 do
      let s = String.concat "," labels.(q).(q') in
      if s <> "" then
        fprintf out "%i -> %i [ label = \"%s\" ];\n" q q' s
    done
  done;
  fprintf out "}\n";
  close_out out

let genere_pdf input_file output_file =
  Sys.command (Printf.sprintf "dot -Tpdf %s -o %s" input_file output_file)


(*fonction delta_star telle que l’appel delta_star a q u renvoie l’état δ∗(q, u), ou -1 si l’on « sort » de l’automate*)

let rec delta_star (a :afd) (e: etat) (m : mot) =
  match m with
  |[] -> e
  |x :: xs ->
    let e' = a.delta.(e).(x) in
    if e' = -1 then -1 else delta_star a e' xs


(*fonction accepte qui détermine si l’automate accepte ou non le mot passé en
argument*)

let accepte (a : afd) (m : mot) = 
  let e_f = delta_star a a.init m in 
  e_f <> -1 && a.term.(e_f) 

(*fonction accessibles qui prend en entrée un automate a et renvoie un tableau
t de a.n booléens tel que t.(q) indique si l’état q est accessible (depuis l’état initial)*)

let accessibles (a : afd) = 
  let vus = Array.make (a.n) false in 
  let rec explore etat = 
    if not vus.(etat) && etat <> -1 then begin
      vus.(etat) <- true;
      Array.iter explore a.delta.(etat)
    end 
  in explore a.init;
  vus

(*fonction langage_non_vide qui détermine si le langage de l’automate passé en
argument est non vide.*)

let langage_non_vide (a : afd) = 
  let e_acc = accessibles a in 
  let non_vide = ref false in 
  for i = 0 to a.n do 
    if a.term.(i) && e_acc.(i) then non_vide := true
    done;
  !non_vide


(*fonction inverse renvoyant la matrice d’adjacence de G←(A), où A est l’automate passé en argument. On demande une complexité en O(n
2 + nm).*)

let inverse (a : afd) = 
  let graphe = Array.make_matrix a.n a.n false in 
  for etat = 0 to a.n - 1 do
    for elt = 0 to a.m - 1 do 
      let etat_suivant = a.delta.(etat).(elt) in 
      if etat_suivant <> -1 then graphe.(etat_suivant).(etat) <- true
    done;
  done;
  graphe

(*fonction coaccessibles qui détermine les états co-accessibles de l’automate
donné en argument, et donner sa complexité.*)

let coaccessibles (a : afd) = 
  let vus =  Array.make a.n false in 
  let inv = inverse a in
  let rec explore etat = 
    if not vus.(etat) && etat <> -1 then begin
      vus.(etat) <- true;
      for etat_suivant = 0 to a.n - 1 do 
        if inv.(etat).(etat_suivant) then explore etat_suivant
      done;
    end in 
  for final = 0 to Array.length a.term - 1 do 
    if a.term.(final) then explore final
  done;
  vus

(*fonction est_emonde déterminant si son argument est un automate émondé*)

let est_emonde (a : afd) = 
  let vrai = ref true in 
  let acc = accessibles a in 
  let coacc = coaccessibles a in 
  for i = 0 to a.n - 1 do 
    if not (acc.(i) && coacc.(i)) then vrai := false
    done;
  !vrai

(*fonction complementaire prenant en entrée un automate A supposé complet et
renvoyant un automate A′
tel que L(A′
) = L(A)
c
(où le complémentaire est pris dans Σ
=
avec Σ = [0 . . . m − 1])*)

let complementaire (a : afd) = 
  {
   n = a.n;
   m = a.m;
  init = a.init;
  delta = Array.init a.n (fun i -> Array.copy a.delta.(i));
  term = Array.map not a.term;
  }


(*fonction complete qui renvoie un automate complet équivalent à son argument. Il
est inutile de traiter le cas où l’automate de départ est déjà complet comme un cas particulier
(on renverra dans ce cas un automate contenant un état inaccessible).*)

let complete (a : afd) = 
  let delta' = Array.make_matrix (a.n + 1) a.m a.n in 
  let term' = Array.make (a.n  + 1)  false in 
  for etat = 0 to a.n - 1 do 
    term'.(etat) <- a.term.(etat)
  done;
  for etat = 0 to a.n - 1 do 
    for elt = 0 to a.m - 1 do 
      let etat_suivant = a.delta.(etat).(elt) in 
      if etat_suivant = -1 then delta'.(etat).(elt) <- a.n
      else delta'.(etat).(elt) <- etat_suivant
    done
  done;
  {n = (a.n)+1;
  m = a.m;
  init = a.init;
  term = term';
  delta = delta'}

(*fonction auto_inter prenant en entrée deux automates A1 et A2 (que l’on
pourra supposer complets) sur un même alphabet Σ et renvoyant un automate B tel que
L(B) = L(A1) ∩ L(A2).*)

let auto_inter (a1 : afd) (a2 : afd) = 
  let n = a1.n * a1.n in 
  let m = a1.m in 
  let delta = Array.make_matrix n m (-1) in
  let f i j = a1.n * i + j in
  for i = 0 to a1.n - 1 do 
    for j = 0 to a2.n - 1 do 
      for elt = 0 to m - 1 do 
        let etat1 = f i j in 
        let etat2 = f a1.delta.(etat1).(elt) a2.delta.(j).(elt)
      in delta.(etat1).(elt) <- etat2;
     done
    done
  done;
  let init = f a1.init a2.init in 
  let term = Array.make n false in 
  for i = 0 to a1.n - 1 do 
    for j = 0 to a2.n - 1 do 
      term.(f i j) <- a1.term.(i) && a2.term.(j)
    done
  done;
  {n;m;init;term;delta}


let nb_pair_0 = construit {
  initial = 0;
  acceptants = [0];
  transitions = [(0,0,1);(0,1,0);(1,0,0);(1,1,1)]
}

let nb_1_congru_a_2_mod_3 = construit {
initial = 0;
acceptants = [2];
transitions = [(0,0,0);(0,1,1);(1,0,1);(1,1,2);(2,0,2);(2,1,0)]
}

let () = 
  let a_inter = auto_inter nb_pair_0 nb_1_congru_a_2_mod_3 in
  graphviz a_inter "figures/a_inter.viz";
  let _ = genere_pdf "figures/a_inter.viz" "figures/a_inter.pdf"


(*fonction inclus prenant en entrée deux automates (supposés complets) et
déterminant si le langage du premier est inclus dans celui du second.*)

let inclus (a1 : afd) (a2 : afd) = 
  let comp = complementaire a1 in 
  let inter_a2 = auto_inter comp a2 in 
  langage_non_vide inter_a2


(*fonction equivalent prenant en entrée deux automates sur le même alphabet (non nécessairement complets) et déterminant s’ils reconnaissent le même langage.*)

let equivalent a1 a2 =
    let a1_complet = complete a1 in
    let a2_complet = complete a2 in
    inclus a1_complet a2_complet && inclus a2_complet a1_complet