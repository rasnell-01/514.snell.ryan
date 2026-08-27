(* rose.ml
   Question 1: Practice with OCaml Pattern Matching

   A rose tree is a tree in which every node carries a value and has an
   arbitrary (possibly empty) LIST of children, rather than a fixed
   number of children like a binary tree.
*)

type 'a rose = Node of 'a * 'a rose list

(* ------------------------------------------------------------------ *)
(* size : 'a rose -> int
   Number of nodes in the tree.

   A node contributes 1 (itself) plus the sum of the sizes of all of
   its children. We fold List.fold_left over the children, running
   size recursively on each one and accumulating the total. *)
let rec size (Node (_, children)) : int =
  1 + List.fold_left (fun acc child -> acc + size child) 0 children

(* ------------------------------------------------------------------ *)
(* map : ('a -> 'b) -> 'a rose -> 'b rose
   Applies f to every value in the tree, preserving its shape.

   We apply f to the value at this node, and recursively map f over
   every child (List.map (map f) children applies the *tree* map to
   each child rose tree). *)
let rec map (f : 'a -> 'b) (Node (x, children)) : 'b rose =
  Node (f x, List.map (map f) children)

(* ------------------------------------------------------------------ *)
(* fold : ('a -> 'b list -> 'b) -> 'a rose -> 'b
   The general catamorphism (fold) for rose trees.

   f is given the value stored at a node, together with the *already
   folded* results for each of that node's children (as a 'b list),
   and must produce the folded result for this node. We first fold
   every child recursively (List.map (fold f) children), then hand
   the node's own value and that list of results to f. *)
let rec fold (f : 'a -> 'b list -> 'b) (Node (x, children)) : 'b =
  f x (List.map (fold f) children)

(* ------------------------------------------------------------------ *)
(* size and map are both easily re-derived from fold, which shows fold
   really is the fundamental recursion principle for this type: *)

let size' (t : 'a rose) : int =
  fold (fun _ child_sizes -> 1 + List.fold_left ( + ) 0 child_sizes) t

let map' (f : 'a -> 'b) (t : 'a rose) : 'b rose =
  fold (fun x child_trees -> Node (f x, child_trees)) t

(* ------------------------------------------------------------------ *)
(* A small helper to pretty-print an int rose tree, purely for the
   test driver below. *)
let rec to_string (Node (x, children)) : string =
  match children with
  | [] -> string_of_int x
  | cs ->
    Printf.sprintf "%d(%s)" x (String.concat ", " (List.map to_string cs))

(* ------------------------------------------------------------------ *)
(* Test driver.
        1
      / | \
     2  3  4
    /|     |
   5 6     7
*)
let t : int rose =
  Node (1, [
    Node (2, [ Node (5, []); Node (6, []) ]);
    Node (3, []);
    Node (4, [ Node (7, []) ]);
  ])

let () =
  Printf.printf "tree            : %s\n" (to_string t);
  Printf.printf "size t          : %d\n" (size t);
  Printf.printf "size' t         : %d\n" (size' t);
  Printf.printf "map (( * )2) t  : %s\n" (to_string (map (fun x -> x * 2) t));
  Printf.printf "map' (( * )2) t : %s\n" (to_string (map' (fun x -> x * 2) t));
  (* sum every value using fold directly *)
  let total = fold (fun x child_sums -> x + List.fold_left ( + ) 0 child_sums) t in
  Printf.printf "fold sum t      : %d\n" total;
  (* max depth using fold directly *)
  let depth =
    fold (fun _ child_depths ->
        1 + List.fold_left max 0 child_depths) t
  in
  Printf.printf "fold depth t    : %d\n" depth;
  (* leaf-only single node *)
  let leaf = Node (42, []) in
  Printf.printf "size (leaf)     : %d\n" (size leaf)
