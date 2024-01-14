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

