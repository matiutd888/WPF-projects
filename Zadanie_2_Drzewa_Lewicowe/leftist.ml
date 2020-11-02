(* Autor: Mateusz Nowakowski *)
(* Code review: Bartosz Ruszewski 418400 grupa 1 *)

(* typ reprezentujacy kolejke, jezeli kolejka jest niepusta
    kolejne elementy oznaczaja: 
    lewe poddrzewo, wartosc korzenia (elementu
    o najwyzszym priorytecie), prawe poddrzewo oraz
    'prawa wysokosc' kolejki.
    Pusta kolejke reprezentuje Empty_queue *)
type 'a queue =
    | Node of 'a queue * 'a * 'a queue * int 
    | Empty_queue

let empty = Empty_queue

exception Empty

let is_empty q =
    if q = empty then true
    else false

(* zwraca 'prawa wysokosc' drzewa *)
let height q = 
    match q with
    | Empty_queue -> 0
    | Node(_, _, _, h) -> h
    
let rec join d1 d2 = 
    match (d1, d2) with
    | Empty_queue, _ -> d2
    | _, Empty_queue -> d1
    | Node(l1, a1, r1, h1), Node(l2, a2, r2, h2) ->
        if a1 > a2
            then join d2 d1
        else
            let d3 = join r1 d2 in 
            match d3 with
            | Empty_queue -> raise Empty                
            | Node(l3, a3, r3, h3) ->
                let h_ld1 = height l1 in
                if h_ld1 < h3 
                    then Node(d3, a1, l1, h_ld1 + 1)
                else Node(l1, a1, d3, h3 + 1)

let add a q =
    join (Node(empty, a, empty, 1)) q

let delete_min q = 
    match q with
    | Empty_queue -> raise Empty
    | Node(l, x, r, _) -> (x, join l r)

(* koniec programu *)

(* testy *)

let b = add 1 empty;;
let b = add 3 b;;
let b = add (-1) b;;
let b = add 2 b;;
let b = add 1 b;;

let c = add 10 empty;;
let c = add (-5) c;;
let c = add 1 c;;
let c = add 4 c;;
let c = add 0 c;;

let b = join b c;;

let (a,b) = delete_min b;;
assert (a = (-5));;

let (a,b) = delete_min b;;
assert (a = (-1));;

let (a,b) = delete_min b;;
assert (a = 0);;

let (a,b) = delete_min b;;
assert (a = 1);;

let (a,b) = delete_min b;;
assert (a = 1);;

let (a,b) = delete_min b;;
assert (a = 1);;

let (a,b) = delete_min b;;
assert (a = 2);;

let (a,b) = delete_min b;;
assert (a = 3);;

let (a,b) = delete_min b;;
assert (a = 4);;

let (a,b) = delete_min b;;
assert (a = 10);;

assert (try let _ = delete_min b in false with Empty -> true);;
