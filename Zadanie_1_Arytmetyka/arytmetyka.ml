(* Autor: Mateusz Nowakowski 418323*)
(* Code review: Bartosz Ruszewski 418400 grupa 1*)

type wartosc = (float * float) list

(* wazne spostrzezenie - podczas uzywania metod zaimplementowanych w programie
    wartosci moga przyjmowac dwie 'postacie'
    1) [(a, b)]
    2) [(neg_infinity, a); (b; infinity)]
    gdzie a jest mniejsze lub rowne b.
    Konsekwencją jest to, że bardzo latwo jest udowodnić poprawność metod 
    rekurencyjnych w module - wystarczy rozwazac wszystkie mozliwe 'postacie' 
    wartosci w metodach *)

(* wyjatek wyrzucany gdy dlugosc listy reprezentujacej wartosc jest dluzsza
    niz przewidywana *)
exception Too_big_list_exception

(* definicja - wartość jest 'spojna', kiedy jej reprezentacja 
    to jednoelementowa lista *)

(* wartosc reprezentujaca nan *)
let wartosc_nan : wartosc = [(nan, nan)]
    
(* zwraca true, jesli wartosc float podana jako argument nie jest skonczona *)
let is_infinite x = (x = infinity) || (x = neg_infinity)

(* zwraca true jesli wartosc float podana jako argument jest rowna nan *)
let is_nan_float x = compare x nan = 0

(* na potrzeby programu uzywam operatora ktory bedzie mnozyl dwie wartosci 
    typu float, 
    i dodatkowo przy mnozeniu wartosci, ktora nie jest skonczona, przez 0, zwroci
    0 *)
let ( ***. ) x y =
    if (x = 0.0 && is_nan_float y <> true) || (y = 0.0 && is_nan_float x <> true)
        then 0.0
    else x *. y

(* ------ KONSTRUKTORY ------ *)

let wartosc_dokladnosc x y =
    if x >= 0. then
        ([((x ***. (100. -. y)) /. 100., (x ***. (100. +. y)) /. 100.)] : wartosc)
    else
        ([(x ***. ((100. +. y) /. 100.), x ***. ((100. -. y) /. 100.))] : wartosc)


let wartosc_dokladna x =
    if not (is_infinite x) then ([(x, x)] : wartosc) 
    else wartosc_nan

(* jezeli ktorakolwiek czesc wartosci jest nieokreslona 
    to cala wartosc jest nieokreslona *)
let wartosc_od_do x y =
    if is_nan_float x || is_nan_float y || x = infinity then wartosc_nan
    else ([(x, y)] : wartosc)

(* ------ /KONSTRUKTORY ------ *)

(* ------ FUNKCJE POMOCNICZE ------ *)

(* okresla 'znak' przedzialu, rozwazajac znaki granic przedzialu pierwszego 
    elementu listy reprezentujacej wartosc x, zastosowanie przy metodzie
    odwrotnosc *)
let znak (x : wartosc) =
    match x with
    | (a, b) :: t ->
        if a >= 0. then 1.
        else if b > 0. then 0.
        else if b = 0. then 0.5
        else (-1.)
    | [] -> 1.
 
(* zwraca true jesli wartosc podana jako argument jest rowna wartosc_nan *)
let is_nan (x : wartosc) =
    match x with 
    | [(a, b)] -> is_nan_float a && is_nan_float b 
    | _ -> false

(* porownoje dwie wartosci *)
let rec compare_wartosc (x : wartosc) (y : wartosc) = 
    match x, y with
    | [], [] -> true
    | (x1, x2) :: tx, (y1, y2) :: ty -> 
        if (x1 = y1 && x2 = y2) 
            then (compare_wartosc tx ty) 
        else false
    | _, _ -> false

(* scala przedzialy wewnatrz wartosci *)
let rec merge (x : wartosc) =
    match x with
    | [] -> []
    | _ :: [] -> x
    | (p0, p1) :: (p2, p3) :: [] ->
        if p0 <= p2 && p1 <= p3 then 
            if p1 >= p2 then wartosc_od_do p0 p3 
            else x
        else merge [(p2, p3); (p0, p1)]
    | _ -> raise Too_big_list_exception

(* scala dwie wartosci, zakladajac, że sume przedzialow reprezentujych ja 
    bedzie mozna przedstawic albo w postaci przedzialu spojnego, albo 
    przedzialu w postaci [-inf, a] U [b; inf], co jest warunkiem dzialania metody. 
    Aby udowodnic, ze metoda dziala wystarczy rozpatrzyc wszystkie przypadki x y
    spelniajace warunek wstepny *)
let rec merge2 (x : wartosc) (y : wartosc) =
    if is_nan x || is_nan y then wartosc_nan
    else
        match x with
        | [] -> y
        | [hx] -> 
           (match y with
            | [] -> x
            | [hy] -> merge [hx; hy]
            | hy :: t -> merge2 (merge2 x [hy]) (merge2 x t))
        | hx :: tx -> 
           (match y with
            | [] -> x
            | hy :: ty -> 
                let m = merge2 [hx] [hy] in
                if (compare_wartosc m [hx; hy])
                    then merge2 (merge2 [hx] ty) (merge2 tx [hy])
                else merge2 (merge2 [hx] [hy]) (merge2 tx ty))
            
        
(* mnozy dwa 'spojne' przedzialy, jezeli ktorys z przedzialow jest pusty 
    lub nie jest spojny zwraca wyjatek *)
let razy_simple (x : wartosc) (y : wartosc) =
    match x, y with
    | [(a, b)], [(c, d)] ->
        let x = min (min (a ***. c) (a ***. d)) 
            (min (b ***. c) (b ***. d))
        and y = max (max (a ***. c) (a ***. d)) 
            (max (b ***. c) (b ***. d))
        in wartosc_od_do x y
    | _, _ -> raise Too_big_list_exception

(* zwraca wynik dzielenia 1/wartosc, przy dzieleniu przez wartosc 
    dokladną 0 zwraca wynik nieokreslony 
    (nan, nan) *)
let rec odwrotnosc (x : wartosc) =
    match x with
    | [] -> []
    | [(0., 0.)] -> wartosc_nan
    | [(a, b)] ->
        let z = znak x in
        if z = 0. then ([(neg_infinity, 1. /. a); (1. /. b, infinity)] : wartosc)
        else if z = 0.5 then [(neg_infinity, 1. /. a)]
        else wartosc_od_do (1. /. b) (1. /. a)
    | h :: t -> merge2 (odwrotnosc [h]) (odwrotnosc t)

(* ------ /FUNKCJE POMOCNICZE ------ *)

(* ------ SELEKTORY ------ *)

let rec in_wartosc (x : wartosc) y =
    match x with
    | [] -> false
    | (p1, p2) :: t ->
        if (y >= p1 && y <= p2) || y = p1 || y = p2 then true
        else in_wartosc (t : wartosc) y

let rec min_wartosc (x : wartosc) =
    match x with 
    | [] -> neg_infinity 
    | (p1, _) :: _ -> p1

let rec max_wartosc (x : wartosc) =
    match x with
    | [] -> infinity
    | [(_, p1)] -> p1
    | (_, _) :: t -> max_wartosc t

let sr_wartosc (x : wartosc) =
  let mini = min_wartosc x and maxi = max_wartosc x 
  in (mini +. maxi) /. 2.

(* ------ /SELEKTORY ------ *)

(* ------ DZIAŁANIA ------ *)

let rec plus (x : wartosc) (y : wartosc) =
    match x with
    | [] -> y
    | [(x1, x2)] -> 
       (match y with
        | [] -> x
        | [(y1, y2)] -> merge (wartosc_od_do (y1 +. x1) (y2 +. x2))
        | h1 :: h2 :: [] ->
            merge2 (plus x [h1]) (plus x [h2]) 
        | _ -> raise Too_big_list_exception)
    | h1 :: h2 :: _ -> 
       (match y with
        | [] -> x
        | [_] -> merge2 (plus [h1] y) (plus [h2] y)
        | _ -> wartosc_od_do neg_infinity infinity)    

let rec razy (x : wartosc) (y : wartosc) =
    match x with
    | [] -> []
    | [_] -> 
       (match y with
        | [] -> []
        | [_] -> razy_simple x y
        | hy :: t -> merge2 (merge (razy x [hy])) (merge (razy x t)))
    | h :: t -> merge2 (razy [h] y) (razy t y)

let podzielic (x : wartosc) (y : wartosc) = 
    razy x (odwrotnosc y)

let minus (x : wartosc) (y : wartosc) =
    plus x (razy y (wartosc_dokladna (-1.)))

(* ------ /DZIAŁANIA ------ *)

(* koniec programu *)

(* testy *)
let a = wartosc_od_do 1. 4.     (* <1.0, 4.0> *)
let b = wartosc_od_do (-.2.) 3. (* <-2.0, 3.0> *)
let c = podzielic a b           (* (-inf, -1/2> U <1/3, inf) *)
let d = podzielic c b           (* (-inf, -1/6> U <1/9, inf) *)
let e = plus d (wartosc_dokladna 1.)             (* (-inf, 5/6> U <10/9, inf) *)
let f = sr_wartosc (podzielic (wartosc_dokladna 1.) 
(wartosc_dokladna 9.));; (* 1/9 *)
assert (is_nan_float (sr_wartosc d));
assert (in_wartosc d 0.12);
assert (not (in_wartosc d 0.));
assert (not (in_wartosc d (-0.125)));
assert (in_wartosc d f);
assert (not (in_wartosc e 1.));;

