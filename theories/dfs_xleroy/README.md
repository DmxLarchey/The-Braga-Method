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

[comment]: <> (DLW->JFM: la remarque sur les cycles et la position de `x::` existait déjà dans le paragraphe suivant et je l'ai complétée.)

We recognize the internally defined `dfs_list` is the particular instance of `foldleft` where `dfs_list = foldleft dfs`. Factoring out this inlining, we get the following variant:
```ocaml
(* DFS variant by X. Leroy nested with foldleft *)
let dfs_xl_fold x =
  let rec dfs x a =
    if x ∈ a then a else x::foldleft dfs (succs x) a
  in dfs x []
```
which we call _external nesting_ of `dfs` with `foldleft`.

From our point of view, that presentation with external nesting, more modular and more compact, would be the favored one.
As to why X. Leroy did not favor this external nesting over the inlined one, we can only speculate:
- this could be related to the target audience which prefers _concrete_ recursion combined with explicit pattern matching 
  over the use of _abstract_ external combinators like `fold` or even `map`;
- but also, we spot a technical difficulty that could have prevented him from considering the external nesting _at the Coq level_, a difficulty that we already encountered ourselves (with eg. unbounded minimisation or iterations of partial recursive functions) and which is the following:
  - `foldleft` is a _higher-order_ function while `dfs_list` is just _first-order_;
  - while it is easy to write down `fold_left` in Coq (it is actually part of the `List` module in the standard library), this function cannot be applied to DFS because DFS is inherently a partial function, and `fold_left` assumes a total function as input parameter;
  - Ocaml does not distinguish partial functions from total function, but in Coq, partial functions are represented as total functions restricted by propositional pre-conditions;
  - hence we need to define a Coq version of `foldleft` which is not only partial, but of which _the input parameter `f` itself is a partial function_. Hence, in Coq we need  `foldleft` as a partial polymorphic higher order function;
- willingly or not, X. Leroy circumvents this issue by inlining the nesting of `foldleft dfs` as `dfs_list` in the code of `dfs_xl_inld` itself:
  in that case `dfs_list` is still partial, but first-order only as it does not have to deal with a partial function as first argument.

As a consequence, at the price of some slight redundancies, we deal with both external nesting and inlined nesting in a symmetric way
in this presentation. 

[comment]: <> (_JFM->DLW: je serais bcp + prudent là-dessus._ 

_Il y a toute une communauté de programmeurs, à laquelle X s'adresse aussi, qui préfèrent récursivité+filtrage explicite aux combinateurs dont surtout fold, qui est plus obscur que map par ex. : primo il y a foldleft et foldright, qui est Qui ? Deuzio il faut en plus se rappeler l'ordre de paramètres (aucun ordre n'est naturel, on le voit bien). Tertio la récursivité et le filtrage séparément sont plus flexibles et se comprennent bien séparément. Quatro l'abstraction c'est bien une fois qu'on est parfaitement habitué, mais on finit par perdre le fil, cf les constructions catégoriques. Et tout ça pour avoir au final qqchse qui n'est pas plus puissant est est plutôt moins expressif, par ex. qiand on veut récurrer sur une composante de profondeur plus que 1. C'est pour ça que Coq, parti des combinateurs à la système-T, a évolué vers Fixpoint+garde. En pratique la plupart reviewer industriels de base (que X semble avoir en tête dans son discours) préfèreront un code dans le style qu'il utilise pour CoqPL24 qu'avec foldleft._

_Pour nous c'est un peu différent : 1/ pouvoir traiter fold(left) a un intérêt général indépendant, là on a un bon terrain d'expérience et on est très contents de voir Braga fonctionner dessus ; 2/ ce qui est naturel est de dériver le pgm en style fixpoint à partir du pgm avec foldleft, pas l'inverse. Mais on ne doit pas imposer nos biais._

_Je serais donc partisan de mettre les versions `XXX_fold` et `XXX_inld` sur un pied d'égalité, en indiquant qu'on traite indifféremment l'une et l'autre et que chacun(e) pourra adopter le style qu'il ou elle préfère, et que de plus nous savons gérer leur équivalence. cela attirera plus de public._

_DLW->JFM: j'ai modéré les affirmations en tenant compte de ce que tu as écrit. Je suis d'accord avec tes arguments. Dis-moi si ça te convient. Ok pour traiter `xxx_fold` et `xxx_inld` de manière symmétrique._

_JFM->DLW: désolé j'avais oubié de répondre danss ce README, étant immergé dans le code. Pour moi c'est tout bon._)

### The nested algorithm `dfs_cycle` compared to `dfs_xl`

In the code of `dfs_xl_fold`, we observe that in the internal `dfs` loop, the current node `x` is prepended using `x::_` to the result, but _too late_: precisely, this is done _after_ the successors of `x` are themselves visited, which prevents the algorithm to detect a possible repetition of `x` and thus avoid cycling forever. 

The same remark of course applies to the code of `dfs_xl_inld` where `dfs_list` is just the inlining of `foldleft dfs`. We will indeed prove that `dfs_xl`, ie both algorithms, are suitable for DAGs only. 
 
A slight change provides a version of DFS which will avoid this behavior and which we call `dfs_cycle`. The easiest way to observe the change is on the externally nested variant, where we prepending of `x::_` occurs before starting traverse its successors: ie `x::(foldleft dfs (succs x) a)` is replaced with
`foldleft dfs (succs x) (x::a)`. This gives us to following code:
```ocaml
(* DFS variant of dfs_xl_fold which accommodates with cycles *)
let dfs_cycle_fold x =
  let rec dfs x a =
    if x ∈ a then a else foldleft dfs (succs x) (x::a)
  in dfs x []
```
but this works just as well on the inlined nested variant:
```ocaml
(* Variant of dfs_cycle_fold with inlined nesting *)
let dfs_cycle_inld x =
  let rec dfs x a =
    if x ∈ a then a else
      let rec dfs_list l a = match l with
      | []   -> a
      | y::l -> dfs_list l (dfs y a)
      in dfl_list (succs x) (x::a)
  in dfs x []
```

This slight update from `dfs_xl` to `dfs_cycle`  has a significant impact on the semantics:
- the output list is different, in particular, on its order,
- but also, critically, the precondition for termination is now more permissive, 
  ie. `dfs_cycle` accepts graphs that do contain cycles, hence its name.

We establish these formally. 

### The recursive terminal algorithm `dfs_book`

In the Braga book chapter however, we studied the following variant of DFS
```ocaml
(* DFS variant as described in the Braga book chapter *)
let dfs_book x =
  let rec dfs a = function
  | []   -> a
  | x::l -> if x ∈ a then dfs a l else dfs (x::a) (succs x @ l)
  in dfs [] [x]
```
that uses list append (denoted infix as `@`) as an external tool (of linear complexity). Notice that the internal loop `dfs` in `dfs_book` is _not a nested algorithm_ and it is moreover a recursive terminal algorithm. Also, the accumulator `a` which collects already visited nodes in the internal `dfs` appears first in `dfs_book` whereas it appears last for `dfs_xl` and `dfs_cycle`.

[comment]: <> (DLW->JFM: c'est fait j'ai remonté `dfs_braga` et maintenant renommé `dfs_cycle_fold`. Je préfère que tu partes de celui-là pour tes transformations car il me semble plus facile d'expliquer la différence avec `dfs_xl_fold`. JFM->DLW: d'ac pour partir dans le README de `dfs_cycle_fold` car c'est plus compact et trivialement dérivable seult dans cette direction; mais la différence est la même.
JFM->DLW: dfs_inloop est aligné, y compris ses commentaires introductifs.)

It is not immediate that `dfs_book` and `dfs_cycle` compute the same thing which means that they both have the same domain of termination and output exactly the same list, but we mechanise this proof and show their equivalence.
This equivalence can be proved directly, but we get more information by showing how `dfs_book` can be
derived from `dfs_cycle` by a chain of simple transformations; at each step we show that the next program is
equivalent to to previous one.

## Further Variations
To complete our exploration, we also study the following variants of `dfs_xl` and `dfs_cycle`, with _self-nesting_ of their internal loop `dfs_list`:
```ocaml
let dfs_xl_self x =
  let rec dfs_list l a = match l with 
  | []   -> a
  | x::l -> dfs_list l (if x ∈ a then a else x::dfs_list (succs x) a)
  in dfs_list [x] []
```

## From `dfs_cycle_fold` to `dfs_book`

[comment]: <> (_DLW->JFM: pourquoi ne pas introduire `dfs_cycle_inld` ici tout simplement? Ca éviterait de la repéter et ca le raproche de `dfs_cycle_self` que l'on peut aussi introduire ici, histoire de voir les transformations successives_
_JFM->DLW: en y repensant ce matin, je ne préfère pas, d'où mon parag ci-dessus qui parle de "pied d'égalité"_)

Interestingly, `dfs_book` can be derived from `dfs_cycle_fold` using few number of semantic preserving elementary transformations. Remind that, starting from `dfs_cycle_fold`, we get `dfs_cycle_inld` by specializing/inlining `foldleft`.
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
Then `dfs_cycle_self'` is obtained by replacing `dfs x` by `dfs_list [x]` and 
expanding the body of `dfs` inside `dfs_list`:
```ocaml
let dfs_cycle_self x =
  let rec dfs_list l a = match l with
  | []   -> a
  | x::l -> if x ∈ a then dfs_list l a 
            else dfs_list l (dfs_list (succs x) (x::a))
  in dfs_list [x] []
```

[comment]: <> (_DLW->JFM: peut-être revoir la numérotation des étapes. Aussi est-ce qu'on a intérêt à swap l'ordre des arguments où alors on change `dfs_book` pour éviter le changement au milieu ?_
JFM->DLW : en fait comme l'ordre des arg est une question secondaire, je m'étais
déjà aligné sur ton code avec l'accu en dernier arg partout depuis un moment,
ce qui simplifie le code+commentaire ci-dessus. Je mets le code qui suit à jour.
Je préfère aussi que `dfs_book` garde l'accu en dernier.)

The third step is a little bit more technical: the (implicit) stack of recursive calls is implemented using an explicit stack of lists `s`; in particular nested recursive calls are eliminated.
```ocaml
let dfs_cycle_stack x =
  let rec dfs_list_stack l s a = match l with
  | []   -> (match s with
    | []   -> a
    | l::s -> dfs_list_stack l s a)
  | x::l -> fun s ->
    if x ∈ a then dfs_list_stack l s a
    else dfs_list_stack (succs x) (l::s) (x::a)
  in dfs_list_stack [x] [] []
```
Fourth step: `l` and `s` are grouped into a single list of lists `ls` which represents `l::s`:
```ocaml
let dfs_book_eff x =
  let rec dfs_stack s a = match s with
  | []         -> a
  | []::[]     -> a
  | []::s      -> dfs_stack s a
  | (x::l):: s ->
    if x ∈ a then dfs_stack (l::s) a
    else dfs_stack (succs x :: l :: s) (x::a)
  in dfs_stack [[x]] []
```
The latter program can be actually seen as a variant of `dfs_book` which is somewhat more efficient since its avoids calculations of list concatenations, hence its name.
Indeed, we finally obtain `dfs_book` by flattening `s`, so that `(x :: l) :: s`is represented by `x :: ls`, with `ls := l @ s` and `succs x :: l :: s` is represented by `succs x @ ls`.
```ocaml
let dfs_book x =
  let rec dfs_flatten lls a = match ls with
  | []     -> a
  | x::ls ->
    if x ∈ a then dfs_flatten ls a
    else dfs_flatten (succs x @ ls) (x::a)
  in dfs_flatten [x] []
```

[comment]: <> (_DLW->JFM: une question naturelle c'est: est-ce qu'on peut mener la même transformation de code sur `dfs_xl`? On arrive déjà jusqu'à `dfs_xl_self` mais peut-on arriver à du récursif terminal ? Est-ce que ma chaine suivante marche pex? J'ai l'impression que non. Parce que le `a` dans `dfs_xl_flatten` ne change jamais..._

_JFM->DLW: il faut une stack plus complexe, qui se rappelle de `x :: _`. Moi je le fais au nez, c'est plus amusant, mais je suis à peu près sûr qu'il existe une théorie académique pour ça; c'est de la compil._

_DLW->JFM: oui ça me rappelle des notions de dérécursivation mais ça serait bien d'expliquer pourquoi ça marche avec un nested comme `dfs_cycle_self` et pas avec `dfs_xl_self` parce qu'il n'est pas terminal ?_

_JFM->DLW: si si ça marche aussi pour `dfs_xl_self` sur le même principe : l'idée est que la pile
contient les instructions sur la suite à donner à un résultat intermédiaire (plus exactement
un codage concret qui les reflète) ; pour `dfs_cycle_self` c'est toujours un appel à `dfs_list`
tandis que pour `dfs_xl_self` ce peut être aussi une construction
`x :: _`, donc là il faut une pile d'éléments à 2 cas, que l'on peut optimiser
car ces cas apparaissent forcément en alternance.
On passe d'abord de self' à self en sortant le if.
Par contre on s'arrête à eff, pas de flatten (sauf trafiquage de peu d'intérêt
a priori)._)

```ocaml
let dfs_xl_inld x =
  let rec dfs x a =
    if x ∈ a then a else
      let rec dfs_list l a = match l with
      | []   -> a
      | y::l -> dfs_list l (dfs y a)
      in x::dfl_list (succs x) a
  in dfs x []

let dfs_xl_self' x =
  let rec dfs_list l a = match l with
  | []   -> a
  | x::l -> dfs_list l (if x ∈ a then a else x::dfs_list (succs x) a)
  in dfs_list [x] []

let dfs_xl_self succs =
  let rec dfs_list l a = match l with
  | []   -> a
  | x::l ->
    if in_dec x a then dfs_list l a
    else dfs_list l (x :: dfs_list (succs x) a)
  in fun x -> dfs_list [x] []
dfs_list [] [x]

(* stack *)
type 'a elt = Econs of 'a | Edl of 'a list
type 'a stack = Emp | Push of 'a elt * 'a stack

let dfs_xl_eff succs =
  let rec dfs_list_stack l s a = match l with
  | []   ->
      (match s with
       | Emp -> a
       | Push (Econs x, s) -> dfs_list_stack [] s (x :: a)
       | Push (Edl l, s) -> dfs_list_stack l s a
      )
  | x::l ->
    if in_dec x a then dfs_list_stack l s a
    else dfs_list_stack (succs x) (Push (Econs x, Push (Edl l, s))) a
  in fun x -> dfs_list_stack [x] Emp []

(* optim stack *)
type 'a stack2 = Emp2 | Push2 of 'a * 'a list * 'a stack2

let dfs_xl_eff2 succs =
  let rec dfs_list_stack2 l s a = match l with
  | []   ->
      (match s with
       | Emp2 -> a
       | Push2 (x, l, s) -> dfs_list_stack2 l s (x :: a)
      )
  | x::l ->
    if in_dec x a then dfs_list_stack2 l s a
    else dfs_list_stack2 (succs x) (Push2 (x, l, s)) a
  in fun x -> dfs_list_stack2 [x] Emp2 []
```

