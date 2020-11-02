(* Autor: Mateusz Nowakowski *)
(* Code Review: Dominik Wiśniewski *)

type point = float * float

type kartka = point -> int

(* epsilon wprowadzony dla dokladnosci przy porownywaniu
    dwoch liczb zmiennoprzecinkowych *)
let e = 10e-9

(* funkcja przyjmuje jako argumenty punkty P Q,
    zwraca wektor PQ reprezentowany jako punkt *)
let minus (a, b) (c, d) = (c -. a, d -. b)

(* dodaje dwa wektory reprezentowane jako punkty *)
let plus (a, b) (c, d) = (a +. c, b +. d)

(* funkcja przyjmuje jako argument wektor reprezentowany jako punkt
    zwraca kwadrat jego dlugosci *)
let dist_squared (a, b) = a *. a +. b *. b

let prostokat (a, b) (c, d) = function (x, y) ->
    if a -. e <= x && x <= c +. e && b -. e <= y && y <= d +. e then 1
    else 0

let kolko s r = function p ->
    if dist_squared (minus s p) <= r *. r +. e then 1
    else 0

(* det p1 p2 p3 sprawdza 
    po ktorej stronie wektora p1p2 lezy p3.
    Jezeli det p1 p2 p3 jest:
        - rowny 0, to p1 p2 p3 sa wspoliniowe
        - wiekszy od 0, to p3 lezy po lewej stronie p1 p2
        - mniejszy od 0, to p3 lezy po prawej stronie p1 p2 *)
let det (x1, y1) (x2, y2) (x3, y3) = 
    x1 *. y2 +. x2 *. y3 +. x3 *. y1 -. (x2 *. y1 +. x3 *. y2 +. x1 *. y3)

(* odbicie_sym p1 p2 p3 zwraca odbicie symetryczne punktu p3 wzgledem prostej 
    wyznaczanej przez p1 p2 *)
let odbicie_sym (x1, y1) (x2, y2) (x, y) = 
    let (d_x, d_y) = (x2 -. x1, y2 -. y1) in
    if d_x = 0. then (2. *. x1 -. x, y) 
    else if d_y = 0. then (x, 2. *. y1 -. y)
    else let a = d_y /. d_x in
    let b = y1 -. a *. x1 in
    let a_p = - 1. /. a in
    let b_p = y -. a_p *. x in
    let x_p = (b_p -. b)/.(a -. a_p) in
    let y_p = a *. x_p +. b in
    let v_p = minus (x, y) (x_p, y_p) in
        (plus (x_p, y_p) v_p)

let zloz p1 p2 k = function p ->
    let d = det p1 p2 p in
    if abs_float d < e then k p
    else if d < 0. then 0
    else let q = odbicie_sym p1 p2 p in
        (k p + k q)

let skladaj l k = 
    List.fold_left (fun a (p1, p2) -> zloz p1 p2 a) k l

(* testy *)

let zle = ref 0
let test n b =
  if not b then begin
    Printf.printf "Zly wynik testu %d!!\n" n;
    incr zle
  end

let epsilon = 0.0001

let (=.) x y = (x-.epsilon <= y) && (y <= x+.epsilon)

let a = (1., 1.);;
let b = (10., 10.);;
let c = (5., 5.);;
let d = (5., 1.);;
let e = (5., 10.);;
let x = (5., 11.);;
let y = (0., 10.);;

let f = prostokat a b;;

test 1 (f a = 1);;
test 2 (f b = 1);;
test 3 (f c = 1);;
test 4 (f d = 1);;
test 5 (f e = 1);;
test 6 (f x = 0);;
test 7 (f y = 0);;

let g = zloz d c f;;

test 8  (g a = 2);;
test 9  (g b = 0);;
test 10 (g c = 1);;
test 11 (g d = 1);;
test 12 (g e = 1);;
test 13 (g x = 0);;
test 14 (g y = 1);;

let h = zloz (1., 3.) (6., 3.) g;;

test 15 (h a = 0);;
test 16 (h b = 0);;
test 17 (h c = 2);;
test 18 (h d = 0);;
test 19 (h e = 1);;
test 20 (h x = 0);;
test 21 (h y = 1);;
test 22 (h (1., 5.) = 4);;
test 23 (h (0., 4.) = 2);;
test 24 (h (3., 4.) = 4);;
test 25 (h (5., 3.) = 1);;
