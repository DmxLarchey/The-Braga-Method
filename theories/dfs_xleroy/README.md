# Variations of DFS algorithms and the Braga method

## Introduction

The motivation for this study is the CoqPL 2024 paper _[Well founded recursion done right](https://popl24.sigplan.org/details/CoqPL-2024-papers/2/Well-founded-recursion-done-right) by Xavier Leroy_, which elaborates on a Depth First Search algorithm (DFS) in its appendix B, called `dfs_xl` herein. Although this algorithm is explicitly dedicated to direct acyclic graphs (DAGs), it is easy to see how a slight mutation in a single line (of the intended extracted code) of `dfs_xl` allows one to recover a DFS without restriction (called `dfs_cycle` herein).

In the [_Braga method book chapter_](https://www.worldscientific.com/doi/abs/10.1142/9789811236488_0008) (see also the [Braga method on GitHub](https://github.com/DmxLarchey/The-Braga-Method/)), we extensively studied another DFS algorithm simply called `dfs` there but herein called `dfs_book` for disambiguation.

It was thus natural for us to (and we felt compelled to):
- see how the Braga method instantiates on `dfs_xl` which is a nested recursive algorithm, in contrast with `dfs_book` which is simply recursive, and even tail-recursive;
- compare the semantics of `dfs_xl` and `dfs_book`:
  + ie. their respective domains of termination;
  + and the respective specifications of their output;
- instantiate the Braga method on `dfs_cycle` as well (the slightly modified variant of `dfs_xl`) and study its relationship with `dfs_book`; the latter turns out to be retrieved step by step from `dfs_cycle` using simple transformations, but the semantic equivalence can also be justified using tools developed for the Braga method.
 
Notice that general DFS algorithms are inherently partial algorithms:
- when the type of vertices is infinite, there can be a cycle-free infinite path in the graph;
  + typically, if the _successors_ of `x` is the list `[1+x]` over natural number nodes, then no call to DFS can terminate;
  +  in this case, the domain of any DFS algorithm should be empty;
- when the type of vertices is finite, the `dfs_book` algorithm of the Braga chapter, `dfs_cycle` and their variations always terminate;
- in contrast, the `dfs_xl` algorithm studied by X. Leroy  and its variations further require DAGs otherwise they may loop forever on some inputs.

We establish all these properties in Coq as the by product of _certification by extraction_ of correct by construction programs, which is the overall framework of the Braga method.

## Requisites

Below we assume the following overall parameters in which all the DFS algorithms we discuss are parametric:
```
succs : 𝓥 -> 𝓥 list
∈ : 𝓥 -> 𝓥 list -> bool
```
where `𝓥` is a type of vertices, `succs` describes a finitely branching directed graph structure (but not necessarily finite or acyclic though), and `∈` is a membership test for lists, abstracted of the specificities of its implementation, and denoted with an infix notation.

We will also sometimes need the following polymorphic implementation of the higher-order function `foldleft`
```ocaml
(* foldleft : (β -> α -> α) -> β list -> α -> α *)
let rec foldleft f l a = match l with
| []   -> a
| y::l -> foldleft f l (f y a)
```
which only differs from the Ocaml one `List.fold_left` in the order of parameters of both `foldleft` itself (`l` and `a` are switched), and of its function argument `f` (of which the two input are switched accordingly). 

## Presentation of the various DFS algorithms

### The nested algorithm `dfs_xl`

Given these assumptions, the algorithm studied by X. Leroy in CoqPL 2024 could be described as the following Ocaml program. Notice that _only its Coq enrichment is actually written in the paper_:
```ocaml
(* DFS variant by X. Leroy as in CoqPL'2024 *)
let dfs_xl_inld x =
  let rec dfs x a =
    if x ∈ a then a else
      let rec dfs_list l a = match l with
      | []   -> a
      | y::l -> dfs_list l (dfs y a)
      in x::dfl_list (succs x) a
  in dfs x []
```
and we qualify this form as an _inlined nesting_ of `dfs` with `dfs_list` (see below). 

_(** There, the accumulator in the last recursive call is unchanged, which prevents the algorithm to discover a cycle in the previously visited nodes. *)_
_DLW->JF: Je ne suis pas convaincu par cet argument. L'appel de `(dfs y a)` dans `dfs_list` modifie l'accumulateur._

We recognise the internally defined `dfs_list` is the particular instance of `foldleft` where `dfs_list = foldleft dfs`. Factoring out this inlining, we get the following variant:
```ocaml
(* DFS variant by X. Leroy nested with foldleft *)
let dfs_xl_fold x =
  let rec dfs x a =
    if x ∈ a then a else x::foldleft dfs (succs x) a
  in dfs x []
```
which we call _external nesting_ of `dfs` with `foldleft`.

One could wonder why X. Leroy did not favor this external nesting (more compact, modular) over the inlined one. We speculate that there was a technical difficulty that prevented him from doing so, a difficulty that we already encountered ourselves (with eg. unbounded minimisation of partial recursive function) and which is the following:
- `foldleft` is a higher-order function while `dfs_list` is just first-order;
- while it is easy to write down `fold_left` in Coq (it is actually part of the Standard Library), this total function cannot be applied to DFS because DFS is inherently a partial function;
- Ocaml does not distinguish partial functions from total function, but in Coq, partial functions are represented as total functions restricted by propositional pre-conditions;
- hence we need to define Coq version of `foldleft` which is not only partial, but of which _the input parameter `f` itself is a partial function_. Hence, in Coq we need  `foldleft` as a partial polymorphic higher order function;
- X. Leroy circumvents this issue by inlining the nesting of `foldleft dfs` as `dfs_list` in the code of `dfs_xl_inld` itself;
- in that case `dfs_list` is still partial, but first-order, and does not need to deal with a partial function as first argument.

### The nested algorithm `dfs_cycle`

Another observation that could be made regarding `dfs_xl` is the position where `x` is prepended to the already visited nodes using `x::_`. In `dfs_xl` this occurs after the successors of `x` are visited by `foldleft dfs (succs x) a`, hence we speculate that when `dfs` visits a node contained in a cycle, the algorithm will loop forever. We will indeed prove that `dfs_xl` is for DAGs only. 
 
A slight change provides a version of DFS which will avoid this behavior and which we call `dfs_cycle`. The easiest way to observe the change is on the externally nested variant:
```ocaml
(* DFS variant of dfs_xl_fold which accommodates with cycles *)
let dfs_cycle_fold x =
  let rec dfs x a =
    if x ∈ a then a else foldleft dfs (succs x) (x::a)
  in dfs x []
```
but the inlined nested variant works just as well:
```ocaml
(* Variant of dfs_cycle with inlined nesting *)
let dfs_cycle_inld x =
  let rec dfs x a =
    if x ∈ a then a else
      let rec dfs_list l a = match l with
      | []   -> a
      | y::l -> dfs_list l (dfs y a)
      in dfl_list (succs x) (x::a)
  in dfs x []
```

### The recursive terminal algorithm `dfs_book`

In the Braga book chapter however, we study the following variant of DFS
```ocaml
(* DFS variant as described in the Braga book chapter *)
let dfs_book x =
  let rec dfs a = function
  | []   -> a
  | x::l -> if x ∈ a then dfs a l else dfs (x::a) (succs x@l)
  in dfs [] [x]
```
that uses list append/`@` as an external tool (of linear complexity). Notice that the internal loop `dfs` in `dfs_book` is _not a nested algorithm_ and it is moreover a recursive terminal algorithm. Also, the accumulator `a` which collects already visited nodes in the internal `dfs` appears first in `dfs_book` whereas it appears last for `dfs_xl` and `dfs_cycle`.

_JFM->DLW : arrivé ici je me rends compte que sauf erreur de ma part on parle de `dfs_cycle`, sous la forme avec foldleft. Il me paraît plus judicieux d'introduire soit cette variante `_fold`, soit  celle "nested" inspirée de XL dès le début `_inld`, comme ce que j'ai ajouté. Pour l'instant je laisse ce qui suit, mais peut-être que la suite plus bas pourra être allégée. Mes transfos partent de `dfs_cycle_inld` mais comme on dérive plus facilement ce dernier de `dfs_cycle_fold` (par dépliage de foldleft) que l'inverse, on peut prendre `dfs_cycle_fold`  comme pt de départ. Et du coup je remonter le code de `dfs_braga_cycle` plus haut._
_DLW->JFM: c'est fait j'ai remonté `dfs_braga` et maintenant renommé `dfs_cycle_fold`. Je préfère que tu partes de celui-là pour tes transformations car il me semble plus facile d'expliquer la différence avec `dfs_xl_fold`.
JFL->DLW: d'ac pour partir dans le README de `dfs_cycle_fold` car c'est plus compact
et trivialement dérivable seult dans cette direction; mais la différence est la même._

It is not immediate that `dfs_book` and `dfs_cycle` compute the same thing which means that they both have the same domain of termination and output exactly the same list, but we mechanise this proof and show their equivalence.

## Comparisons of `dfs_xl` and `dfs_cycle`

On the contrary, `dfs_xl` and `dfs_cycle` compute different outputs but also do not have the same domains of termination. We establish this formally. 

If we compare the respective codes of the most compact variants `dfs_xl_fold` and `dfs_cycle_fold`, we notice that the difference is only in the position of `x::_`, ie when the current node of the graph is prepended to the accumulator or output:
- in `dfs_xl_fold    : ... x::(foldleft dfs (succs x) a) ...`;
- in `dfs_cycle_fold : ... foldleft dfs (succs x) (x::a) ...`.

Of course, the same mutation operates on the variants expressed with nested recursion:
- in `dfs_xl_inld    : ... x::(dfs_list (succs x) a) ...`;
- in `dfs_cycle_inld : ... dfs_list (succs x) (x::a) ...`.

This change has a significant impact on the semantics:
- on the order of the output list of course,
- but mainly the weakest precondition for termination (wrt. cycles in the graph).

## Further Variations
_JFM->DLW : il faut revoir la fin en fonction des modifs précédentes , pour inclure les variations que je t'ai indiquées (0/ à 5/). Je dois relire ce qui suit et te laisse d'abord voir ce qui précéde._

_JFM->DLW : finalement j'ai intégré ma partie, j'espère que c'est compatible avec ce que tu voulais._

To complete our exploration, we also study the following variants of `dfs_xl` with _self-nesting_ of its internal loop `dfs`:
```ocaml
let dfs_xl_self x =
  let rec dfs_list l a = match l with 
  | []   -> a
  | x::l -> dfs_list l (if x ∈ a then a else x::dfs_list (succs x) a)
  in dfs_list [x] []
```
Interestingly, the self nested variant `dfs_cycle_self` is the first step towards a variant of  `dfs_book` called `dfs_book_eff` (it is somewhat more efficient since its avoids computating the concatenation of lists) and then `dfs_book` itself. _DLW->JFM: préciser le sens ici...
JFM->DLW: le sens de ? En tout cas j'ai renommé `dfs_cycle_grp` qui n'était pas très heureux_
```ocaml
let dfs_cycle_self x =
  let rec dfs_list a = function
  | []   -> a
  | x::l -> dfs_list (if x ∈ a then a else dfs_list (x::a) (succs x)) l
  in dfs_list [x] []
```
In the second step, the (implicit) stack of recursive calls is implemented using an explicit stack of lists `s`; in particular nested recursive calls are eliminated.
```ocaml
let dfs_cycle_stack x =
  let rec dfs_list_stack a = function
  | []   -> (function
    | []   -> a
    | l::s -> dfs_list_stack a l s)
  | x::l -> fun s ->
    if x ∈ a then dfs_list_stack a l s
    else dfs_list_stack (x::a) (succs x) (l::s) 
  in dfs_list_stack [] [x] []
```
Next step: `l` and `s` are grouped into a single list of lists `ls` which represents `l::s`:
```ocaml
let dfs_book_eff x =
  let rec dfs_stack a = function
  | []         -> a
  | []::ls     -> dfs_stack a ls
  | (x::l)::ls ->
    if x ∈ a then dfs_stack a (l::ls)
    else dfs_stack (x::a) (succs x::l::ls) 
  in dfs_stack [] [[x]]
```
Finally `dfs_book` is obtained by flattening `ls`, so that `(x::l)::ls`is represented by `x::lls` and `succs x::l::ls` is represented by `succs x @ lls` and `lls` is renamed as just `l`.
Next step: `l` and `s` are grouped into a single list of lists `ls` which represents `l::s`:
```ocaml
let dfs_book x =
  let rec dfs_flatten a = function
  | []         -> a
  | x::lls ->
    if x ∈ a then dfs_flatten a lls
    else dfs_flatten (x::a) (succs x::lls) 
  in dfs_flatten [] [x]
```



