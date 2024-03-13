let rec in_dec x l =
  match l with
  | []   -> false
  | y::m -> x = y || in_dec x m;;

in_dec 1 [0;1;2];;
in_dec 1 [0;2];;

let rec dfs_xl succ x accu =
  if in_dec x accu then accu
  else
    let rec dfs_list l accu =
      match l with 
      | []   -> accu
      | y::m -> dfs_list m (dfs_xl succ y accu)
    in x::dfs_list (succ x) accu;;

let rec foldleft f x l =
  match l with
  | []   -> x
  | y::m -> foldleft f (f x y) m;;

let dfs_fl succ =
  let rec dfs_acc a x =
    if in_dec x a then a
    else x::foldleft dfs_acc a (succ x)
  in dfs_acc [];; 

let rec dfs_rev succ a x =
  if in_dec x a then a
  else foldleft (dfs_rev succ) (x::a) (succ x);; 

let rec rev_acc a l =
  match l with
  | []   -> a
  | x::m -> rev_acc (x::a) m;;

let rev = rev_acc [];;

(* dfs_braga reversed *)
let dfs_br succ a x = rev (dfs_rev succ a x);; 

(* For the following graph:

                 4 
            +----+----+
            2         3
         +--+--+   +--+--+
         0     1   1     2
                       +-+-+  
                       0   1

   The prefix order is:
     - left -> right [4;2;0;1;3]
     - right -> left [4;3;2;1;0]

   dfs_xl outputs [4;3;2;1;0] (prefix RL)
   dfs_fl outputs [4;3;2;1;0] (prefix RL)
   dfs_br outputs [4;2;0;1;3] (prefix LR)

 *)

let test n =
  let succ x = if x > 1 then [x-2;x-1] else []
  in  (dfs_xl succ n [],
       dfs_fl succ n,
       dfs_br succ [] n) ;;
       
test 4;;
     
(* For the following graph, dfs_[xl,fl]
   output neither the LR nor the RL prefix
   order :
   
                 4 
            +----+----+
            3         2
         +--+--+   +--+--+
         2     1   1     0
       +-+-+  
       1   0

   The prefix order is:
     - left -> right [4;3;2;1;0]
     - right -> left [4;2;0;1;3]

   dfs_xl outputs [4;3;2;0;1] (neither LR nor RL)
   dfs_fl outputs [4;3;2;0;1] (neither LR nor RL)
   dfs_br outputs [4;3;2;1;0]) (prefix LR)
   *)
  
let test_rev n =
  let succ x = if x > 1 then [x-1;x-2] else []
  in  (dfs_xl succ n [],
       dfs_fl succ n,
       dfs_br succ [] n);;
       
test_rev 4;;

(* So neither dfs_xl nor dfs_fl (which compute the same
   list) output the prefix traversal. However, it seems
   dfs_br ouputs the prefix left-right traversal (after
   reversal of the output list. This remains to be
   established with a proof. *)

let rec rev_acc a l =
  match l with
  | []   -> a
  | x::m -> rev_acc (x::a) m;;

let rev l = rev_acc [] l;;

let foldleft f =
  let rec loop l a = match l with
  | []   -> a
  | x::m -> loop m (f x a)
  in loop;;

let foldnum f =
 let rec loop n l a = match l with
 | []   -> a
 | x::m -> loop (1+n) m (f (n,x) a)
 in loop 0;;

foldnum (fun (n,_) a -> n::a) [0;0;0;0;0;0] [];;

let dfs_cycle succs x =
  let rec dfs x a =
    if in_dec x a then a
    else foldleft dfs (succs x) (x::a)
  in dfs x [];;

let dfs_cycle_br succs x =
  let rec dfs b (n,x) (a,ab) =
    if in_dec x a then (a,ab)
    else foldnum (dfs (n::b)) (succs x) (x::a,(n::b)::ab)
  in dfs [] (0,x) ([],[]);;

let rec dfs_cyc succs =
  let rec dfs a = function
  | []   -> a
  | y::l -> if in_dec y a then dfs a l
            else dfs (y::a) (succs y @ l)
  in fun x -> dfs [] [x];;

(* l is a list of (nodes,path) *)

let map_n f = 
  let rec loop n = function 
  | []   -> []
  | x::l -> (f n x)::loop (n+1) l
  in loop 0;;

let dfs_cyc_br succs =
  let rec dfs a ab = function
  | []       -> ab
  | (y,p)::l -> if in_dec y a then dfs a ab l
                else let succs_paths = map_n (fun n s -> (s,p@[n])) (succs y) in
                     dfs (y::a) (p::ab) (succs_paths @ l)
  in fun x -> dfs [] [] [(x,[])];;
  
let dfs_cyc_paths succs =
  let rec dfs a ab = function
  | []          -> ab
  | (x,p,y)::l -> if in_dec y a then dfs a ab l
                  else let succs_paths = map_n (fun n z -> (x,p@[n],z)) (succs y) in
                       dfs (y::a) ((x,p,y)::ab) (succs_paths @ l)
  in fun x -> dfs [] [] [(x,[],x)];;
                   
let rev_map f =
  let rec loop a = function
  | []   -> a
  | x::l -> loop (f x::a) l
  in loop [];;

let head = function
| []   -> assert false
| x::_ -> x;;

let tail = function
| []    -> []
| _ ::l -> l;;

let rec nth n l =
  if n = 0 then head l 
  else nth (n-1) (tail l);;

let find succs =
  let rec loop x = function
  | []   -> x
  | n::l -> loop (nth n (succs x)) l
  in loop;;

let test s =
  let succs x = if x > 2 then [x-3;x-2;x-1] else [] in 
  let (a,ab) = dfs_cycle_br succs s in  
  let br = dfs_cyc_br succs s in
  let dfs   = rev a in
  let paths = rev_map (fun l -> tail (rev l)) ab in
  let nodes = rev (rev_map (find succs s) paths)
  in (dfs,paths,nodes, rev br);;

(* It looks like dfs_cycle_br computes:
   - the nodes in prefix left/right order
   - the ordered list of smallest paths corresponding 
     to thoses nodes, for lexicographic ordering *)
 
test 5;;


