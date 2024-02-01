
let t1 = Tree (1,[Tree (2,[Tree (4,[]);Tree (5,[])]);Tree (3,[])]);;

let rec bfs a = function 
| []            -> List.rev a
| Tree (i,l)::m -> bfs (i::a) (m@l);;

bfs [] [t1];;

type 'a tree = Tree of 'a * ('a tree list);;

let ht t =
  let rec loop n = function
  | []       -> n
  | None::[] -> n
  | None::m  -> loop (1+n) (m @ [None])
  | Some (Tree (i,l))::m 
             -> loop n (m @ List.map (fun t -> Some t) l)
  in loop 0 [None;Some t];;

(* Using JC idea of replacing None/Some with
   two list, n(ext) level and c(urrent level,
   and using the fact that the height does not
   depend on the order between the siblings,
   we can avoid external functions. The termination
   could certainly be measure based. *)

let rec rev_app a = function
| []   -> a
| x::l -> rev_app (x::a) l;;

let ht t =
  let rec level h n = function
  | []            -> next h n 
  | Tree (_,l)::c -> level h (rev_app n l) c
  and next h n = match n with
  | [] -> h 
  | _  -> level (1+h) [] n
  in level 1 [] [t];;

let leaf = Tree (0,[]);;
let left t = Tree (0,[t;leaf]);;
let right t = Tree (0,[leaf;t]);;

let tree_of_ht =
  let rec loop b n =
    if n = 1 then leaf
    else (if b then left else right) (loop (not b) (n-1)) 
  in loop true;;

let rec list_an a n =
  if n = 0 then []
  else a::list_an (a+1) (n-1);;

let t n = Tree (0,List.map tree_of_ht (list_an 1 (n-1)));;

ht (tree_of_ht 200);;
