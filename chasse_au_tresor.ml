let u_tab = Array.make 1000000 0;;

let calc_u = 
  let u0 = 42 in
  let multiplieur = 19999999 in 
  let modulo = 19999981 in
  u_tab.(0) <- u0;
  for i = 1 to 1000000 - 1 do 
    u_tab.(i) <- (multiplieur * u_tab.(i - 1)) mod modulo
  done;
  u_tab;;

calc_u;;
(*
print_int (u_tab.(123) mod 1000);;
print_newline ();;
print_int (u_tab.(456) mod 1000);;
print_newline ();;
print_int (u_tab.(789) mod 1000);;
*)

let vt_value i p = if (u_tab.(i) mod 10000) < p then 1 else 0;;

let calc_v_tab n p = 
  Array.init (n*n) (fun i -> vt_value i p);;

let count_edges n p = 
  let v_tab = calc_v_tab n p  in 
  let counter = ref 0 in 
  for i = 0 to n * (n-1)/2 do 
    if v_tab.(i) = 1 then incr counter
    done;
  !counter;;


let explicit_graph n p =
  let tab = Array.make n [] in 
  let v_tab = calc_v_tab n p in
  let k = ref 0 in 
  for i = 0 to n - 1 do 
    for j = i + 1 to n - 1 do 
      if v_tab.(!k) = 1 then
        begin 
          tab.(i) <- j  ::  tab.(i); 
          tab.(j) <- i :: tab.(j)
        end;
      incr k
    done;
  done;
  tab;;

let connex_to_0 n p = 
  let g = explicit_graph n p in 
  let seen = Array.make n false in 
  let counter = ref 0 in 
  let rec explore s = 
    if not seen.(s) then begin 
      seen.(s) <- true;
      incr counter;
      List.iter explore g.(s)
    end;
  in explore 0;
  !counter;;


let count_connex_parts n p = 
  let g = explicit_graph n p in 
  let seen = Array.make n false in 
  let count = ref 0 in 
  let rec explore s = 
    if not seen.(s) then begin 
      seen.(s) <- true;
      List.iter (fun s' -> explore s') g.(s)
    end;
  in explore 0;
  for i = 1 to n - 1 do 
    if not seen.(i) then begin
      incr count;
      explore i
    end;
  done;
  !count;;

let explicit_graph_v2 n p k = 
  let tab = Array.make n [] in 
  let v_tab = calc_v_tab n p in
  let k = ref 0 in 
  for i = 0 to n - 1 do 
    if i < n - 1 then begin
      tab.(i) <- (i + 1) :: tab.(i);
      tab.(i + 1) <- i :: tab.(i + 1);
    end;
    for j = i + 1 to n - 1 do 
      if v_tab.(!k) = 1 then
        begin 
          tab.(i) <- j  ::  tab.(i); 
          tab.(j) <- i :: tab.(j)
        end;
      incr k
    done;
  done;
  tab;;

let g_test = 
  let g = Array.make 7 [] in
  g.(0) <- [1;2;4];
  g.(1) <- [0;2;5;6];
  g.(2) <- [0;1;3;4];
  g.(3) <- [2;4];
  g.(4) <- [0;3;5];
  g.(5) <- [1;2;4;6];
  g.(6) <- [1;5];
  g;;

let print_tab tab = 
  for i = 0 to Array.length tab - 1 do
    let txt = if tab.(i) then "true |"  else "false |" in  
    Stdlib.print_string txt;
  done;
  print_newline ();;

let print_q q = 
  let cop = Queue.copy q in 
  while not (Queue.is_empty cop) do 
    let x = Queue.pop cop in 
    Printf.printf "%d |" x;
  done;
  print_newline ();
  print_newline ();;

exception FoundObjective of (int * int);;
let closest_objective g s k objectives_completed =
  (*Printf.printf "Sommet initial : %d" s;
  print_newline ();*)
  let n = Array.length g in
  let seen = Array.make n false in 
  let dist = ref 0 in
  let q = Queue.create () in 
  Queue.push (-1) q;
  let ajoute v = 
    if not seen.(v) then begin
      seen.(v) <- true;
      Queue.push v q
    end
  in ajoute s;
  while not (Queue.is_empty q) do
    (*print_q q;*) 
    match Queue.pop q with
    |(-1) -> incr dist
    |w -> begin
        if (w >= n - k && (not objectives_completed.(w))) then raise (FoundObjective (w,!dist));
        List.iter ajoute g.(w);
        Queue.push (-1) q
      end
  done;;

let nb_moves n p k = 
  let g = explicit_graph_v2 n p k in
  (*let g = g_test in*)
  let objectives_completed = Array.make n false in 
  let total_moves = ref 0 in
  let temp_s = ref 0 in 
  for i = 0 to k - 1 do
    try 
      closest_objective g !temp_s k objectives_completed;
    with
    |FoundObjective(s,d) -> 
      (*Printf.printf "Sommet : %d, à distance %d du sommet %d" s d !temp_s;*)
      print_newline ();
      objectives_completed.(s) <- true;
      temp_s := s;
      total_moves := !total_moves + d;
      (*Printf.printf "Total : %d" !total_moves;*)
      print_newline ();
  done;
  !total_moves;;

print_int (nb_moves 100 32 10);;
print_newline ();;
(*
print_newline ();;
print_newline ();;
print_newline ();;
print_int (count_edges 10 654);;
print_newline ();;
print_int (count_edges 100 543);;
print_newline ();;
print_int (count_edges 1000 12);;
print_newline ();;
print_newline ();;
print_newline ();;
print_int (connex_to_0 10 654);;
print_newline ();;
print_int (connex_to_0 100 543);;
print_newline ();;
print_int (connex_to_0 1000 12);;
print_newline ();;
print_newline ();;
print_newline ();;
print_int (nb_moves 100 32 10);;*)