(* Autor: Mateusz Nowakowski 
    Code review: Jakub Panasiuk *)

(* stan zlewek w programie reprezentowany jest przez tablicę intów, w której na
    i-tej pozycji jest poziom wody w i-tej zlewki *)
       
(* 'dodaj cc h q ile w' sprawdza czy stan zlewek cc znajduje się w
    hashtablicy h. Jeśli nie, to dodaje stan cc do h i parę (cc, ile + 1)
    do kolejki q. ((cc, ile + 1) oznacza, ze stan cc mozemy osiagnac 
    po ile + 1 ruchach). W przeciwnym wypadku cc był już osiągnięty więc 
    nie trzeba go nigdzie dodawać.
    funkcja zwraca 'true', jeśli stan cc jest równy stanowi końcowemu 'w',
    w przeciwnym wypadku zwraca 'false' *)
let dodaj cc h q ile w = 
    if not (Hashtbl.mem h cc) then
        begin Hashtbl.add h cc ();
        Queue.add (cc, ile + 1) q; end;
    cc = w
        
(* Tworzy nowy stan cc powstały z nalania wody z kranu do pełna do m-tej zlewki 
    w stanie zlewek c. Możemy go osiągnąć po 'ile + 1' ruchach.
    Jesli taki stan cc nie był osiągany wcześniej, 
    dodaje go do hashtablicy h i kolejki q *) 
let do_pelna m c l h q ile w =
    let cc = Array.copy c in
    cc.(m) <- l.(m);
    dodaj cc h q ile w

(* Tworzy nowy stan cc powstały z wylania wody z m-tej zlewki
    w stanie zlewek c. Możemy go osiągnąć po 'ile + 1' ruchach.
    Jesli taki stan cc nie był osiągany wcześniej, 
    dodaje go do hashtablicy h i kolejki q *)     
let do_zlewu m c h q ile w = 
    let cc = Array.copy c in
    cc.(m) <- 0;
    dodaj cc h q ile w
    
(* Tworzy nowy stan cc powstały z przelania wody z q-tej zlewki
    do p-tej zlewki w stanie zlewek c. 
    Możemy go osiągnąć po 'ile + 1' ruchach.
    Jesli taki stan cc nie był osiągany wcześniej, 
    dodaje go do hashtablicy h i kolejki queue *) 
let z_jednej_do_drugiej p q c l h queue ile w = 
    let cc = Array.copy c in
    if cc.(p) + cc.(q) > l.(p) then
        begin
            cc.(q) <- cc.(q) - l.(p) + cc.(p);
            cc.(p) <- l.(p)
        end
    else begin
            cc.(p) <- cc.(p) + cc.(q);
            cc.(q) <- 0
         end;
    dodaj cc h queue ile w

    
(* oblicza NWD liczb a i b *)
let rec nwd a b = 
    if b = 0 then a 
    else nwd b (a mod b)

(* t: tablica par intów, t.(i) = (a_i, b_i),
    Niech n oznacza długość t.
    warunek_nwd t oblicza nwd_t = NWD(a_0, ..., a_(n - 1)) i sprawdza, czy dla 
    każdego b_i różnego od a_i, b_i dzieli się przez nwd_t.
    Jeśli tak - zwraca 'true', w przeciwnym wypadku 'false' *)
let warunek_nwd t = 
    let nwd_t = Array.fold_left (fun acc (a, _) -> nwd acc a)
                (fst t.(0)) t 
    in Array.for_all 
        (fun (a, b) -> 
            if b <> a then b mod nwd_t = 0
            else true) t

(* sprawdza przypadek, w ktorym wszystkie zlewki 
    w stanie końcowym są pełne lub puste
    Jeśli tak jest, zwraca parę 
    (true, 'liczba pełnych zlewek w stanie końcowym').
    W przeciwnym razie zwraca parę (false, -1) *)
let sprawdz_latwe_stany t = 
    if Array.for_all (fun (a, b) -> b = 0 || b = a) t then
        (true, Array.fold_left 
            (fun x (a, b) -> if b <> 0 && a = b then x + 1 else x) 0 t)
    else (false, -1)

(* 'zadanie l w' zwraca minimalną liczbę czynności potrzebną by puste 
    zlewki o pojemnościach reprezentowanych przez tablicę l (l.(i) to pojemność
    i-tej zlewki) doprowadzić do stanu reprezentowanego przez tablicę w. 
    Gdy nie jest to możliwe zwraca -1 *)
let zadanie l w = 
    let n = Array.length l in
    let h = Hashtbl.create (n * n) in
    let q = Queue.create () in
    let rozw = ref (-1) in 
    let czy = ref true in
    Queue.add ((Array.make n 0), 0) q;
    Hashtbl.add h (Array.make n 0) ();
    while not (Queue.is_empty q) && !czy do
        let (c, ile) = Queue.take q in
        for i = 0 to n - 1 do
            if do_pelna i c l h q ile w then
                begin czy := false;
                rozw := ile + 1; end;
            if do_zlewu i c h q ile w then
                begin czy := false;
                rozw := ile + 1; end;
            for j = 0 to n - 1 do
                if i <> j then
                    if z_jednej_do_drugiej i j c l h q ile w then
                        begin czy := false;
                        rozw := ile + 1; end
            done
        done
    done;
    !rozw
    

let przelewanka t = 
    let (lr, wr) = Array.fold_left 
                        (fun (al, aw) (li, wi) -> (li :: al, wi :: aw)) 
                        ([], []) t 
    in let (l, w) = (Array.of_list (List.rev lr),
                     Array.of_list (List.rev wr))
    in let latwe_stany = sprawdz_latwe_stany t 
    in if fst latwe_stany then snd latwe_stany
    else if not (Array.exists (fun (a, b) -> b = 0 || b = a) t) then -1
    else if not (warunek_nwd t) then -1
    else zadanie l w


(* testy *)

(*
let a = [|(10,2);(20,20);(10,0);(1000,1000)|];;
assert ( przelewanka a = -1 );;
let a = [|(3,2);(5,4);(5,2);(6,1)|];;
assert (przelewanka a = -1);;
let a = [|(40,1);(10,4);(23,2);(40,1)|];;
assert (przelewanka a = -1);;
let a = [|(12,2);(6,3);(4,4);(10,2)|];;
assert (przelewanka a = -1);;
let a = [|(14,3);(3,1)|];;
assert (przelewanka a = -1);;
let a = [|(3,2);(3,3);(1,0);(12,1)|];;
assert ( przelewanka a = 4 );;
let a = [|(1,1);(100,99)|];;
assert ( przelewanka a = 2 );;
let a = [|(3,3);(5,4);(5,2);(6,1)|];;
assert (przelewanka a = 6);;
let a = [|(100,3);(2,1);(1,0);(6,1)|];;
assert (przelewanka a = 7);;
let a = [|(3,3);(5,5);(5,5);(6,6)|];;
assert (przelewanka a = 4);;
*)

