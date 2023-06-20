type 'a prop =
  | Top
  | Bot
  | V of 'a
  | Not of 'a prop
  | And of 'a prop * 'a prop
  | Or of 'a prop * 'a prop
  | Impl of 'a prop * 'a prop


type 'a sequent = {
  gamma : 'a prop list;
  delta : 'a prop list;
  gamma_var : 'a prop list;
  delta_var : 'a prop list
}

(*fonction create_sequent : 'a prop list -> 'a prop list -> 'a sequent telle que
create_sequent l_gamma l_delta renvoie un 'a sequent dont les champs gamma_var et delta_var
sont des listes vides, et les champs gamma et delta contiennent les listes passées en arguments*)

let create_sequent gamma delta = 
  {gamma = gamma; delta = delta;gamma_var = []; delta_var = []}

(* fonction member : 'a -> 'a list -> bool qui teste si un élément est dans une liste*)

let rec member elt lst = 
  match lst with
  |[] -> false
  |x :: xs -> x = elt || member elt xs

(*fonction bot : 'a sequent -> bool qui teste si la règle (⊥) peut être appliquée au
séquent pris en argument*)

let bot seq = 
  member Bot seq.gamma || member Bot seq.gamma_var

(*fonction top : 'a sequent -> bool qui teste si la règle (⊤) peut être appliquée au
séquent pris en argument*)

let top seq = 
  member Top seq.delta || member Top seq.delta_var

(*fonction axiom : 'a sequent -> bool qui teste si la règle (Ax) est applicable au séquent
pris en argument*)

let axiom seq = 
  let rec aux gamma delta = 
    match gamma with 
    |[] -> false
    |formule :: reste_gamma ->  
      member formule delta || aux reste_gamma delta 

  in aux seq.gamma seq.delta || aux seq.gamma_var seq.delta || aux seq.gamma seq.delta_var || aux seq.gamma_var seq.delta_var


(*fonction and_gamma : 'a sequent -> 'a sequent qui renvoie la prémisse de la règle
(∧ ⊢) appliquée à la première formule du champ gamma du séquent pris en argument.
On lèvera l’exception Wrong_rule "And Gamma" si cette formule n’est pas une conjonction*)

exception Wrong_rule of string

let and_gamma seq = 
  match seq.gamma with 
  |And(f1,f2) :: reste ->
    {gamma = f1 :: f2 :: seq.gamma;
    delta = seq.delta;
    gamma_var = seq.gamma_var;
    delta_var = seq.delta_var} 
  |_ -> raise (Wrong_rule "AND GAMMA")

(*fonction or_gamma : 'a sequent -> 'a sequent * 'a sequent qui renvoie les prémisses
de la règle (∨ ⊢) appliquée à la première formule du champ gamma du séquent pris en argument.
On lèvera l’exception Wrong_rule "Or Gamma" si cette formule n’est pas une disjonction*)

let or_gamma seq = 
  match seq.gamma with 
  |Or(f1,f2) :: reste -> 
    let seq1 = 
    {gamma = f1 :: seq.gamma;
    delta = seq.delta;
    gamma_var = seq.gamma_var;
    delta_var = seq.delta_var}
    in 
    let seq2 = 
      {gamma = f2 :: seq.gamma;
      delta = seq.delta;
      gamma_var = seq.gamma_var;
      delta_var = seq.delta_var}
    in (seq1,seq2)
  |_ -> raise (Wrong_rule "OR GAMMA")

(*fonction impl_gamma : 'a sequent -> 'a sequent * 'a sequent qui renvoie les prémisses de la règle (→ ⊢) appliquée à la première formule du champ gamma du séquent pris en
argument.
On lèvera l’exception Wrong_rule "Impl Gamma" si cette formule n’est pas une implication*)

let impl_gamma seq = 
  match seq.gamma with 
  |Impl(f1,f2) :: reste -> 
    let seq1 = 
      {gamma = reste;
      delta = f1 :: seq.delta;
      delta_var = seq.delta_var;
      gamma_var = seq.gamma_var}
    in let seq2 = 
      {gamma = f2 :: reste;
      delta = seq.delta;
      delta_var = seq.delta_var;
      gamma_var = seq.gamma_var}
    in (seq1,seq2)
  |_ -> raise (Wrong_rule "IMPL_GAMMA")

(*fonction not_gamma : 'a sequent -> 'a sequent qui renvoie la prémisse de la règle
(¬ ⊢) appliquée à la première formule du champ gamma du séquent pris en argument.
On lèvera l’exception Wrong_rule "Not Gamma" si cette formule n’est pas une négation*)

let not_gamma seq = 
  match seq.gamma with 
  |Not(f1) :: reste -> 
    {gamma = reste;
    gamma_var = seq.gamma_var;
    delta = f1 :: seq.delta;
    delta_var = seq.delta_var}
  |_ -> raise (Wrong_rule "NO GAMMA ?")

(*fonction and_delta : 'a sequent -> 'a sequent * 'a sequent qui renvoie les prémisses de la règle (⊢ ∧) appliquée à la première formule du champ delta du séquent pris en
argument.
On lèvera l’exception Wrong_rule "And Delta" si cette formule n’est pas une conjonction*)

let and_delta seq = 
  match seq.delta with  
  |And(f1,f2) :: reste -> 
    let seq1 = 
      {gamma = seq.gamma;
      gamma_var = seq.gamma_var;
      delta = f1 :: seq.delta;
      delta_var = seq.delta_var}
    in let seq2 = 
      {gamma = seq.gamma;
      gamma_var = seq.gamma_var;
      delta = f2 :: seq.delta;
      delta_var = seq.delta_var}
    in (seq1,seq2)
  |_ -> raise (Wrong_rule "bonsoir non")

(*fonction or_delta : 'a sequent -> 'a sequent qui renvoie la prémisse de la règle (⊢ ∨)
appliquée à la première formule du champ delta du séquent pris en argument.
On lèvera l’exception Wrong_rule "Or Delta" si cette formule n’est pas une disjonction*)

let or_delta seq = 
  match seq.delta with 
  |Or(f1,f2) :: reste -> 
    {gamma = seq.gamma; 
    gamma_var = seq.gamma_var;
    delta = f1 :: f2 :: seq.delta;
    delta_var = seq.delta_var}
  |_ -> raise (Wrong_rule "non")

(*fonction impl_delta : 'a sequent -> 'a sequent qui renvoie la prémisse de la règle
(⊢→) appliquée à la première formule du champ delta du séquent pris en argument.
On lèvera l’exception Wrong_rule "Impl Delta" si cette formule n’est pas une implication*)

let impl_delta seq =
  match seq.delta with 
  |Impl(f1,f2) :: reste ->
    {gamma = f1 :: seq.gamma;
    gamma_var = seq.gamma_var;
    delta= f2 :: reste;
    delta_var = seq.delta_var}
  |_ -> raise (Wrong_rule "impl_delta")

(*fonction not_delta : 'a sequent -> 'a sequent qui renvoie la prémisse de la règle
(⊢ ¬) appliquée à la première formule du champ delta du séquent pris en argument.
On lèvera l’exception Wrong_rule "Not Delta" si cette formule n’est pas une négation.*)

let not_delta seq = 
  match seq.delta with
  |Not(f1) :: reste -> 
    {gamma = f1 :: seq.gamma;
    delta = reste;
    gamma_var = seq.gamma_var;
    delta_var = seq.delta_var}
  |_ -> raise (Wrong_rule "not_delta")

(*fonction proof_search : 'a sequent -> bool qui renvoie true si le séquent pris en
argument est valide, et false sinon, en implémentant la stratégie présentée précédemment*)

let rec proof_search sequent = 
  axiom sequent || bot sequent || top sequent (*on règle direct les cas faciles*)
  ||
  match sequent.gamma with
  |f :: reste -> 
    begin 
    match f with 
    |And(f1,f2) -> proof_search (and_gamma sequent)
    |Or(f1,f2) ->
      let sequent1,sequent2 = or_gamma sequent in proof_search seq1 && proof_search seq2
    |Not(f1) -> proof_search (not_gamma sequent)
    |Impl(f1,f2) -> 
      let sequent1,sequent2 = impl_gamma sequent in proof_search sequent1 && proof_search sequent2
    end;
  |[] -> 
    begin(*rien dans gamma, du coup on teste delta*)
    match sequent.delta with 
    | f :: reste ->
      begin
      match f with
      | And(f1,f2) ->
        let sequent1,sequent2 = and_delta sequent in proof_search sequent1 && proof_search sequent2
      | Or(f1,f2) -> proof_search (or_delta sequent)
      | Impl(f1,f2) -> proof_search (impl_delta sequent)
      | Not(f1) -> proof_search (not_delta f1)
      end
      |[] -> false (*on a rien non plus, c'est forcément faux*)
    end;



let print_proof_result gamma delta =
  let result = proof_search (create_sequent gamma delta) in
  if result then Printf.printf "Séquent valide.\n%!"
  else Printf.printf "Séquent non valide.\n%!"


let test () =
  (* Exemples invalides *)
  print_proof_result [] [Or(V 1, V 1)];
  print_proof_result [] [Impl(Impl(Impl(V 1, V 2),V 1),V 2)];

  (* Exemples valides *)
  print_proof_result [] [Or(V 1, Not(V 1))];
  print_proof_result [] [Impl(Impl(Impl(V 1, V 2),V 1),V 1)];
  print_proof_result [And(And(V 1, V 2), V 3)] [And(V 1, And(V 2, V 3))];
  print_proof_result [Or(Or(V 1, V 2), V 3)] [Or(V 1, Or(V 2, V 3))];
  print_proof_result [Impl(V 1, V 2)] [Impl(Not(V 2), Not(V 1))];
  print_proof_result [Impl(Not(V 2), Not(V 1))] [Impl(V 1, V 2)];
  print_proof_result [V 1; V 2] [Impl(V 3, And(V 1, V 3))];