(* Autor: Mateusz Nowakowski *)
(* Code Review: Stanisław Gutowski *)

open PMap

exception Cykliczne

(* zwraca parę, której pierwszym elementem jest mapa,
    w ktorej kluczami są etykiety (np czynności) a wartościami 
    kolejne liczby naturalne. Drugim elementem jest lista w której n-tym
    elementem jest etykieta, której w mapie przypisana jest wartość n *)
let make_map list =
    let map = ref (create Pervasives.compare) in
    let i = ref 0 in
    let rev_map = ref [] in
    let add_list l = 
        List.iter 
            (fun x -> 
                if not (mem x !map) then
                    begin
                        map := add x !i !map;
                        rev_map := x :: !rev_map;
                        i := !i + 1;
                    end
                else ()) l
    in 
    List.iter (fun x -> 
            if not (mem (fst x) !map) then
                begin
                    map := add (fst x) !i !map;
                    rev_map := (fst x) :: !rev_map;
                    i := !i + 1
                end;
            add_list (snd x)) list;
    (!map, List.rev !rev_map)

(* 'make_graph list' zwraca parę, której pierwszym elementem jest lista 
    reprezentująca graf reprezentujący zależności elementów 'list';
    Każdej etykiecie występującej w 'list' przypisana jest liczba naturalna.
    Drugim elementem pary, ktorą zwraca make_graph jest lista, której n-tym 
    elementem jest etykieta w 'list' którą reprezentuje liczba n *)
let make_graph list =
    let (map, odwz) = make_map list in
    let n = List.length odwz in
    let graph = ref (Array.make n (0, [])) in
    let add_list_to_graph v l = 
        begin
            let i = find v map in
            let lista_sasiadow =  
                List.fold_left (fun acc x -> (find x map) :: acc) 
                    (snd !graph.(i)) l  
            in !graph.(i) <- (i, lista_sasiadow);
        end 
    in
    List.iter (fun x -> add_list_to_graph (fst x) (snd x)) list;
    (!graph, odwz)

(* liczba n w liscie kolejnosc reprezentuje n-ty 
	element w tablicy etykiet odwz. 
    'odwzoruj odwz kolejnosc' zwraca listę etykiet w takiej kolejności, 
    w jakiej wystepują liczby reprezentujące je w tablicy kolejnosc *)
let odwzoruj odwz kolejnosc = 
    List.rev (List.fold_left (fun a x -> odwz.(x) :: a) [] kolejnosc)  
    
let topol l = 
    let dfs g odwz =
        let n = Array.length g in
        let visited = Array.make n false in
        let przetwarzane = Array.make n false in
        let kolejnosc = ref [] in
        let rec odwiedz v = 
            if not visited.(v) then
                begin 
                    if przetwarzane.(v) then raise Cykliczne;
                    przetwarzane.(v) <- true;
                    List.iter odwiedz (snd g.(v));
                    kolejnosc := v :: !kolejnosc;
                    visited.(v) <- true;
                    przetwarzane.(v) <- false;
                end
            else ()
        in  Array.iter (fun x -> odwiedz (fst x)) g;
        odwzoruj (Array.of_list odwz) !kolejnosc
    in let (a, b) = make_graph l 
    in dfs a b

(* testy *)

exception WA

let test graph order =
  let hashtbl = Hashtbl.create (List.length order)
  in
  List.iteri (fun i x -> Hashtbl.add hashtbl x i) order;
  let check_one (v, l) =
    List.iter (fun u ->
      if (Hashtbl.find hashtbl v) > (Hashtbl.find hashtbl u)
      then raise WA;) l
  in
  try (List.iter check_one graph; true)
  with WA -> false

let g = [
  ("1", ["2"; "3"]);
  ("3", ["2"]);
  ("4", ["3"; "2"])
];;

assert(test g (topol g));;

let g = [
  ("first", ["second"; "fourth"; "eighth"]);
  ("second", ["fourth"; "eighth"]);
  ("third", ["fourth"; "fifth"; "sixth"]);
  ("fourth", ["eighth"]);
  ("fifth", ["sixth"; "seventh"]);
  ("sixth", ["eighth"; "first"]);
  ("seventh", ["eighth"]);
];;

assert(test g (topol g));;

let g = [
  (1, [2; 3]);
  (2, [4]);
  (3, [4]);
  (4, [5; 6]);
  (5, [7]);
  (6, [7]);
];;

assert(test g (topol g));;

let g = [
  (1, [7; 2]);
  (3, [4; 2; 1; 7; 5]);
  (4, [2; 7; 1]);
  (5, [7; 4; 1; 2]);
  (6, [1; 3; 2; 5; 4; 7]);
  (7, [2])
];;


let test_cyklicznosci g =
  try let _ = topol g in false
  with Cykliczne -> true;;

let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3]);
  (2, [5])
];;

assert(test_cyklicznosci g);;

let g = [
  (1, [2; 3; 4]);
  (3, [7; 8]);
  (4, [9; 10]);
  (10, [15; 16]);
  (2, [5; 6]);
  (13, [4; 10]);
  (11, [12]);
  (12, [13; 14]);
  (15, [16; 8]);
  (8, [12])
];;

assert(test_cyklicznosci g);;
