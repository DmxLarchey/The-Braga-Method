type 'a rtree = Rt of 'a * ('a rtree list);;

let t1 = Rt (1,[Rt (2,[Rt (4,[]);Rt (5,[])]);Rt (3,[])]);;

let leaf x = Rt (x,[]);;
let left x t = Rt (x,[t;leaf 0]);;
let right x t = Rt (x,[leaf 0;t]);;

let rtree_of_ht i =
  let rec loop i b n =
    if n = 1 then leaf i
    else (if b then left i else right i) (loop (1+i) (not b) (n-1)) 
  in loop i true i;;

let rec list_an a n =
  if n = 0 then []
  else a::list_an (a+1) (n-1);;

let t n = Rt (0,List.map rtree_of_ht (list_an 1 (n-1)));;

let rec rev_app a = function
| []   -> a
| x::l -> rev_app (x::a) l;;

(** A recursive terminal BFS algorithm marking the nodes with
    a pair composed of its height and its order in BFS traversal
    order *)
let bfs t =
  let rec level h i a n = function
  | []          -> next (1+h) i a (rev_app [] n)
  | Rt (x,l)::c -> level h (1+i) ((x,(h,i))::a) (rev_app n l) c
  and next h i a n = match n with
  | [] -> rev_app [] a
  | _  -> level h i a [] n
  in level 0 0 [] [] [t];;
		
let t2 = t 3;;
bfs t2;;

