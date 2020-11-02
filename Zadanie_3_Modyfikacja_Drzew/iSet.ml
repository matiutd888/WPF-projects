(*
 * ISet - Interval sets
 * Copyright (C) 1996-2019 Xavier Leroy, Nicolas Cannasse, Markus Mottl,
   Jacek Chrzaszcz, Mateusz Nowakowski
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)


(** Interval Set.

    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint. 

*)

(* Autor: Mateusz Nowakowski *)
(* Code Review: Mateusz Ładysz *)
(* definicja: dwa przedzialy sa rozlaczne wtw gdy nie nalezy ich scalic
	w jeden
	przedzial a 'nachodzi' na b wtw gdy nalezy go scalic z b *)
(* typ drzewa trzymajacego przedzialy
    drzewo puste reprezentuje Empty
    drzewo niepuste reprezentuje Node, kolejne wartosci w Node reprezentuja:
    lewe poddrzewo, trzymana w korzeniu wartosc reprezentujaca przedzial domkniety, 
    prawe poddrzewo, wysokosc drzewa, ilosc trzymanych liczb w lewym poddrzewie,
    ilosc trzymanych liczb w prawym poddrzewie *)
type t =
    | Empty
    | Node of t * (int * int) * t * int * int * int

(* operator bezpiecznego dodawania *)
let (#.) x y =
    if (x > 0 && y > 0 && x + y <= 0)
        then max_int
    else if (x < 0 && y < 0 && x + y >= 0)
        then min_int
    else x + y
    
(* operator bezpiecznego odejmowania *)
let ($.) x y =
    if y = min_int then 
        if x >= 0 then max_int
        else x - y
    else x #. (-y) 

(* pusty set *)    
let empty = Empty

(* zwraca true, jesli przedział jest niepoprawny *)
let invalid (a, b) = b < a

let is_empty t = t = empty

(* zwraca ilosc liczb w drzewie *)
let ilosc_liczb t = 
    match t with
    | Empty -> 0
    | Node(l, (a, b), r, _, x, y) -> x #. y #. (b $. a) #. 1

(* wysokosc drzewa *)
let height = function
    | Node (_, _, _, h, _, _) -> h
    | Empty -> 0

(* buduje drzewo na podstawie poddrzewa i wartosci w korzeniu *)
let make l k r = Node (l, k, r, (max (height l) (height r)) #. 1, 
    ilosc_liczb l, ilosc_liczb r)

(* bal z pSet.ml *)
let bal l k r =
    let hl = height l in
    let hr = height r in
    if hl > hr #. 2 then
        match l with
        | Node (ll, lk, lr, _, _, _) ->
            if height ll >= height lr then make ll lk (make lr k r)
            else
            (match lr with
            | Node (lrl, lrk, lrr, _, _, _) ->
                make (make ll lk lrl) lrk (make lrr k r)
            | Empty -> assert false)
        | Empty -> assert false
    else if hr > hl #. 2 then
        match r with
        | Node (rl, rk, rr, _, _, _) ->
            if height rr >= height rl then make (make l k rl) rk rr
            else
            (match rl with
            | Node (rll, rlk, rlr, _, _, _) ->
                make (make l k rll) rlk (make rlr rk rr)
            | Empty -> assert false)
        | Empty -> assert false
    else make l k r

exception Empty_tree

(* zwraca wartosc w korzeniu lub wyjatek Empty_tree, gdy drzewo jest puste*)
let head s = 
    match s with
    | Empty -> raise Empty_tree
    | Node(l, a, r, h, _, _) -> a

(* funkcja z pSet.ml, usuwa minimalny element z drzewa *)
let rec remove_min_elt = function
    | Node (Empty, _, r, _, _, _) -> r
    | Node (l, k, r, _, _, _) -> bal (remove_min_elt l) k r
    | Empty -> invalid_arg "PSet.remove_min_elt"

(* funkcja z pSet.ml, znajduje najmniejszy element w drzewie *)
let rec min_elt = function
    | Node (Empty, k, _, _, _, _) -> k
    | Node (l, _, _, _, _, _) -> min_elt l
    | Empty -> raise Not_found
  
(* funkcja z pSet.ml, scala dwa drzewa t1 t2 w jedno z założeniem, że
	abs (height t1 - height t2) < 2 i przedzialy na t1 i t2 sa wzajemnie
	rozlaczne *)
let merge t1 t2 =
    match t1, t2 with
    | Empty, _ -> t2
    | _, Empty -> t1
    | _ ->
        let k = min_elt t2 in
        bal t1 k (remove_min_elt t2)

(* zwraca najwiekszy prawy koniec ze wszystkich przedzialow ktore
    nachodza* na przedzial (c, d) lub d jesli taki przedzial nie istnieje 
    * przedzial nachodzi kiedy powinien zostac scalony z (c, d) przy 
    dodawaniu (c, d) do seta *)
let rec znajdz_na_prawo (c, d) s max_r = 
    match s with
    | Empty -> max_r
    | Node(l, (a, b), r, _, _, _) ->
        if d >= b then
            znajdz_na_prawo (c, d) r (max b max_r)
        else if d >= (a $. 1) then
            (max max_r b)
        else znajdz_na_prawo (c, d) l max_r

(* analogicznie do znajdz_na_prawo znajduje najmniejszy lewy koniec ze wszystkich
    przedzialow 'nachodzacych' na (c, d) lub c jesli taki przedzial nie istnieje *)
let rec znajdz_na_lewo (c, d) s min_l = 
    match s with
    | Empty -> min_l
    | Node(l, (a, b), r, _, _, _) ->
        if c <= a  then
            znajdz_na_lewo (c, d) l (min a min_l)
        else if c <= (b #. 1) then
            min min_l a
        else znajdz_na_lewo (c, d) r min_l

(* funkcja porownojaca 'rozlaczne' przedzialy, uzywana w funkcji 
    add_one skopiowanej z pSet.ml *)
let cmp (a, b) (c, d) = 
    if a = c && d = b
        then 0
    else if a < c then -1
    else 1

(* funkcja z pSet.ml, wykorzystywana przy dodawaniu
	przedzialu rozlacznego ze wszystkimi przedzialami w secie *)
let rec add_one x = function
    | Node (l, k, r, h, l1, r1) ->
        let c = cmp x k in
        if c = 0 then Node (l, x, r, h, l1, r1)
        else if c < 0 then
            let nl = add_one x l in
            bal nl k r
        else
            let nr = add_one x r in
            bal l k nr
    | Empty -> Node (Empty, x, Empty, 1, 0, 0)

(* wywoluje add_one *)
let add_pset x set =
    if invalid x then set
    else add_one x set

(* zwraca true jesli przedzialy sa rozlaczne, tj nie nalezy ich scalac *)
let czy_rozlaczne (a, b) (c, d) = 
    if (b #. 1) < c || d < (a $. 1) then true
    else false  

(* znajduje przedzial 'nachodzacy' na interval i zwraca drzewo ktorego
    korzeniem jest ten przedzial lub zbior pusty gdy nie uda 
    sie takiego znalezc *) 
let rec znajdz_nachodzacy s interval = 
    match s with
    | Empty -> s
    | Node(l, x, r, _, _, _) ->
        match (czy_rozlaczne x interval) with
        | true ->
            if cmp x interval < 0 then 
                znajdz_nachodzacy r interval
            else znajdz_nachodzacy l interval
        | false -> s

(* porownuje jedna liczbe z przedzialem, uzywane w mem, below i split *)        
let cmp_jednej_liczby (a, b) x = 
    if x >= a && x <= b then 0
    else if x < a then -1 
    else 1

(* funkcja z pSet.ml, zwraca true jesli element x istnieje w drzewie set,
	false w przeciwnym razie *)    
let mem x set =
    let rec loop = function
        | Node (l, k, r, _, _, _) ->
            let c = cmp_jednej_liczby k x in
            c = 0 || loop (if c < 0 then l else r)
        | Empty -> false in
    loop set

(* funkcja z pSet.ml *)
let iter f set =
    let rec loop = function
        | Empty -> ()
        | Node (l, k, r, _, _, _) -> loop l; f k; loop r in
    loop set

(* funkcja z pSet.ml *)
let fold f set acc =
    let rec loop acc = function
        | Empty -> acc
        | Node (l, k, r, _, _, _) ->
            loop (f k (loop acc l)) r in
    loop acc set

(* funkcja z pSet.ml, zwraca liste elementow set od najmniejszego do 
	najwiekszego *)
let elements set = 
    let rec loop acc = function
        Empty -> acc
        | Node(l, k, r, _, _, _) -> loop (k :: loop acc r) l in
    loop [] set

(* below x s zwraca ilosc elementow w drzewie s mniejszych rownych x *) 
let below x s = 
    let rec below_pom t count = 
        match t with
        | Empty -> count
        | Node(l, (a, b), r, _, cl, cr) -> 
            let c = cmp_jednej_liczby (a, b) x in
            if c = 0 then cl #. count #. (x $. a) #. 1
            else if c = -1 then below_pom l count
            else below_pom r (count #. (b $. a) #. 1 #. cl)
    in below_pom s 0


(* funkcja z pSet.ml *)
let rec join l v r =
    match (l, r) with
        (Empty, _) -> add_pset v r
    | (_, Empty) -> add_pset v l
    | (Node(ll, lv, lr, lh, _, _), Node(rl, rv, rr, rh, _, _)) ->
        if lh > (rh #. 2) then bal ll lv (join lr v r) else
        if rh > (lh #. 2) then bal (join l v rl) rv rr else
        make l v r

(* wywoluje join na secie *)
let join_set l = 
	match l with
	| Empty -> Empty 
	| Node(l, v, r, _, _, _) -> join l v r

(* zmodyfikowany split z pSet.ml *)
let rec split x set =
    let rec loop x = function
        Empty ->
            (Empty, false, Empty)
        | Node (l, v, r, _, _, _) ->
            let c = cmp_jednej_liczby v x in
            if c = 0 then 
                let (a, b) = v in 
                let sr = if x = max_int then empty else add_pset (x #. 1, b) r
                and sl = if x = min_int then empty else add_pset (a, x $. 1) l
                in  (sl, true, sr)
            else if c < 0 then
                let (ll, pres, rl) = loop x l in (ll, pres, join rl v r)
            else
                let (lr, pres, rr) = loop x r in (join l v lr, pres, rr)
    in let setl, pres, setr = loop x set 
    in setl , pres, setr

(* usuwa przedzial (a, b) z drzewa set i zwraca drzewo 
	pozostałe po wykonaniu operacji *)
let rec remove (a, b) set = 
    if invalid (a, b) then set
    else
        match set with
        | Empty -> empty
        | _ ->  let (_, x, r) = split b set
                in let (l, y, _) = split a set 
                in join_set (merge l r)    

(* dodaje przedzial (c, d) do drzewa s, zwraca s z dodanym (c, d) *)
let add (c, d) s = 
    if invalid (c, d) then s
    else
        match s with
        | Empty -> Node(Empty, (c, d), Empty, 1, 0, 0)
        | Node(l, x, r, h, _, _) ->
            let p = znajdz_nachodzacy s (c, d) in
            if p = empty then add_pset (c, d) s
            else
                let minl, maxr = znajdz_na_lewo (c, d) p (min (fst (head p)) c), 
                    znajdz_na_prawo (c, d) p (max (snd (head p)) d)
                in add_pset (minl, maxr) (remove (minl, maxr) s)
    
(* testy *)
let a = add (0, 5) empty;;
let a = add (7, 8) a;;
let a = add (-3, -3) a;;
let a = add (10, 13) a;;
assert(elements a = [(-3, -3); (0, 5); (7, 8); (10, 13)]);;
assert(below 8 a = 9);;
let b = add (6, 6) a;;
let b = remove (6, 6) b;;
let b = add (-100, -5) b;;
let b = add (-4, 6) b;;
assert(elements b = [(-100, 8); (10, 13)]);;
assert(below 10 b = 110);;
let c = remove (2, 10) a;;
assert(elements c = [(-3, -3); (0, 1); (11, 13)]);;
assert(below 12 c = 5);;
