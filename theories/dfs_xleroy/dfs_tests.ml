let rec in_dec x l =
  match l with
  | []   -> false
  | y::m -> x = y || in_dec x m;;

in_dec 1 [0;1;2];;
in_dec 1 [0;2];;

let rec dfs_xl succ x accu =
  if in_dec x accu then accu
  else let rec dfs_list l accu =
         match l with 
         | []   -> accu
         | y::m -> dfs_list m (dfs_xl succ y accu)
       in x::dfs_list (succ x) accu;;

let rec foldleft f x l =
  match l with
  | []   -> x
  | y::m -> foldleft f (f x y) m;;

let rec dfs_fl succ a x =
  if in_dec x a then a
  else x::foldleft (dfs_fl succ) a (succ x);; 

let rec dfs_no_in succ a x =
  x::foldleft (dfs_no_in succ) a (succ x);; 

let rec dfs_rev succ a x =
  if in_dec x a then a
  else foldleft (dfs_rev succ) (x::a) (succ x);; 

let rec dfs_no_in succ a x =
  x::foldleft (dfs_no_in succ) a (succ x);; 

let rec rev_acc a l =
  match l with
  | []   -> a
  | x::m -> rev_acc (x::a) m;;

let rev = rev_acc [];;

let dfs succ a x = rev (dfs_rev succ a x);; 

(* Pour le graphe suivant:

                 4 
            +----+----+
            2         3
         +--+--+   +--+--+
         0     1   1     2
                       +-+-+  
                       0   1

   L'ordre préfixe:
     - gauche->droite [4;2;0;1;3]
     - droite->gauche [4;3;2;1;0]

   L'algo, version X. Leroy renvoie [4;3;2;1;0] 
   Donc ici c'est bien l'ordre préfixe droite -> gauche *)

let test n =
  let succ x = if x > 1 then [x-2;x-1] else []
  in  (dfs_xl succ n [],
       dfs succ [] n) ;;
       
test 4;;
     
(* Ne renvoie pas la liste des noeuds en ordre préfixe
   pour le graphe suivant:
   
                 4 
            +----+----+
            3         2
         +--+--+   +--+--+
         2     1   1     0
       +-+-+  
       1   0
       
   L'ordre préfixe:
     - gauche->droite [4;3;2;1;0]
     - droite->gauche [4;2;0;1;3]

   Mais l'algo, version X. Leroy renvoie [4;3;2;0;1] 
   qui n'est aucun des deux parcours ci-dessus. *)
  
let test_rev n =
  let succ x = if x > 1 then [x-1;x-2] else []
  in  (dfs_xl succ n [],
       dfs succ [] n);;
       
test_rev 4;;

(* Il semble que dfs ... = rev (dfs_rev ...) renvoie
   bien l'ordre préfixe ... à vérfier formellement *)

