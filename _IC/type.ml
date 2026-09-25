"let var(s) = expr head list =
    match list with
    | [] -> None
    | [] :: -> Some x

type 'a box =
    | Box of 'a


'a list
'a option
'a -> 'a
'a -> 'b


let identity x = x

# let id x = x;;
val id : 'a -> 'a = <fun>


'a list -> ('a -> 'b) -> 'b list

('a -> 'b) -> 'a list -> 'b list

List.map string_of_int [1;2;3]

'a = int
'b = string"

Module StringSet = Set.Make(String)

let rec free_vars term =
    match term with
    | Var x ->
        StringSet.singleton x

    | Abs (x, body) ->
        StringSet.remove x (free_vars body)

    | App (t1, t2) ->
        StringSet.union
            (free_vars t1)
            (free_vars t2)

let rec all_vars term =
    match term with
    | Var x -> StringSet.singleton x
    | Abs (x, body) -> StringSet.add (all_vars body)
    | App (t1, t2) -> StringSet.union (all_vars t1) (all_vars t2)

let print_string_set s =
    StringSet.itr
        (fun x -> Printf.printf "%s " x)
        s;
    print_newline ()



let rec size term =
    match term with
    | Var _ ->
        1
    | Abs (_, body) ->
        1 + size body
    | App (t1, t2) ->
        1 + size t1 + size t2



type env = (string * value) list


let make_multiplier =
  fun x ->
    fun y -> x * y
in
let times3 = make_multiplier 3 in
times3 14
