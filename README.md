## Copyright

```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*                 [*] Affiliation LORIA -- CNRS              *)
(*                 [+] Affiliation VERIMAG - Univ. Grenoble   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)
```

## What is this repository for? ###

This repository is gallery of recursive algorithms extracted from Coq
proofs serving as support for the chapter

<div align="center">
<i>The Braga Method: Extracting Certified Algorithms from Complex Recursive Schemes in Coq</i>

by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey) and [Jean François-Monin](http://www-verimag.imag.fr/~monin)
</div>

## How do I set it up? ###

* This code was developed under `Coq 8.11` but should compile from `Coq 8.9+`.
* Compile with
  - `cd theories`
  - `make all`

## The list of examples:

### [Factorial with binary numbers](theories/factb/factb.v)

```ocaml
     (* factb : int -> int *)
     let rec factb n = if n = 0 then 1 else n*factb (n-1)
```

### [List `head`, a simple partial function](theories/head/head.v)

```ocaml
    (* head : α list -> α *)
    let head = function
      | [] -> assert false (* absurd case *)
      | x::_ -> x
```

### [Odd functions on lists](theories/foldl)

```ocaml
    (* with f : β -> α -> β 
        and b0 : β *)
  
    (* foldl_ref : α list -> β *)
    let rec foldl_ref l = match l2r l with
      | Nilr -> b_0
      | Consr (u,z) -> f (foldl_ref u) z
```

### [Unbounded search until a Boolean condition `ns` and `nsa`](theories/ns)

```ocaml
    (* with g : α -> α  
        and b : α -> bool *)

    (* ns : α -> int *)
    let rec ns x = if b x then 0 else 1+ns (g x)

    (* nsa : α -> int -> int *)
    let rec nsa x n = if b x then n else nsa (g x) (1+n) 
```

* [`ns.v`](theories/ns/ns.v): unbounded search `ns` via custom domain predicates 
* [`ns_acc.v`](theories/ns/ns_acc.v): unbounded search `ns` via `Acc`-based domain predicates

### [Depth-First Search on an infinite graph `dfs`](theories/dfs)

```ocaml
    (* with succs : α -> α list
       and  ∈ : α -> α list -> bool *)

    let rec dfs v = function
      | []   -> v
      | x::l -> if x ∈ v then dfs v l else dfs (x::v) (succs x @ l)
```

* [`dfs_graph_def.v`](theories/dfs/dfs_graph_def.v): definition of the computational graph
* [`dfs_fun_bar.v`](theories/dfs/dfs_fun_bar.v): `dfs` via custom domain predicates 
* [`dfs_fun_acc.v`](theories/dfs/dfs_fun_acc.v): `dfs` via `Acc`-based domain predicates
* [`dfs_fun.v`](theories/dfs/dfs_fun.v): _switch_ file for `dfs_fun_[bar,acc].v`
* [`dfs_fix.v`](theories/dfs/dfs_fix.v): fixpoint equations and proof irrelevance for `dfs`
* [`dfs_partial_corr.v`](theories/dfs/dfs_partial_corr.v): partial correctness results for `dfs`
* [`dfs_term.v`](theories/dfs/dfs_term.v): termination characterization and extraction of `dfs`

### [Paulson's If-then-else normalisation `nm`](theories/nm)

```ocaml
    type Ω = α | ω of Ω * Ω * Ω
 
    (* nm : cexpr -> cexpr *)
    let rec nm = function
      | α                => α
      | ω (α,y,z)        => ω (α,nm y,nm z)
      | ω (ω(a,b,c),y,z) => nm (ω(a,nm(ω(b,y,z)),nm(ω(c,y,z)))
```

* [`nm_graph_def.v`](theories/nm/nm_graph_def.v): definition of the computational graph
* [`nm_fun_bar.v`](theories/nm/nm_fun_bar.v): `nm` via custom domain predicates 
* [`nm_fun_acc.v`](theories/nm/nm_fun_acc.v): `nm` via `Acc`-based domain predicates
* [`nm_fun_mid.v`](theories/nm/nm_fun_mid.v): yet another variant of `nm` by JFM
* [`nm_fun.v`](theories/nm/nm_fun.v): _switch_ file for `nm_fun_[bar,acc,mid].v`
* [`nm_fix.v`](theories/nm/nm_fix.v): fixpoint equations and proof irrelevance for `nm`
* [`nm_props_def.v`](theories/nm/nm_props_def.v): partial correctness preliminaries for `nm`
* [`nm_props_ir.v`](theories/nm/nm_props_ir.v): partial correctness results for `nm` via induction-recursion 
* [`nm_props_gr.v`](theories/nm/nm_props_gr.v): partial correctness results for `nm` via graph induction
* [`nm_props.v`](theories/nm/nm_props.v): _switch_ file for `nm_props_[ir,gr].v`
* [`nm_term.v`](theories/nm/nm_term.v): termination characterization and extraction of `nm`

### [First Order Unification `unif`](theories/unif)

```ocaml
    type Λ = Cst of int | Var of int | ⋄ of Λ * Λ

    (* unify : Λ -> Λ -> (int*Λ) list option *)
    unify (Cst c) (M ⋄ N)  = None
    unify (M ⋄ N) (Cst c)  = None
    unify (Cst c) (Var v)  = Some [(v, Const c)]
    unify (M ⋄ N) (Var v)  = if occ-check (Var v) (M ⋄ N) then None else Some [(v, M ⋄ N)]
    unify (Var v) M        = if occ-check (Var v) M       then None else Some [(v, M)]
    unify (Cst c) (Cst d)  = if c = d then Some [] else None
    unify (M ⋄ N) (M'⋄ N') = match unify M M' with
                               | None   -> None
                               | Some υ -> match unify (υ N) (υ N') with
                                 | None   -> None
                                 | Some σ -> Some (σ o υ)
```

* [`unif_graph_def.v`](theories/unif/unif_graph_def.v): definition of the computational graph
* [`unif_fun_bar.v`](theories/unif/unif_fun_bar.v): `unif` via custom domain predicates 
* [`unif_fun_acc.v`](theories/unif/unif_fun_acc.v): `unif` via `Acc`-based domain predicates
* [`unif_fun.v`](theories/unif/unif_fun.v): _switch_ file for `unif_fun_[bar,acc].v`
* [`unif_fix.v`](theories/unif/unif_fix.v): fixpoint equations and proof irrelevance for `unif`
* [`unif_partial_corr.v`](theories/unif/unif_partial_corr.v): partial correctness results for `unif` 
* [`unif_term.v`](theories/unif/unif_term.v): termination characterization and extraction of `unif`

