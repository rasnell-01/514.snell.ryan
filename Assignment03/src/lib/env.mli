(* env.mli

   Question 1: an environment maps variable names to values.

   The four operations below are the interface required by the
   assignment.  The type is abstract on purpose: clients may only build
   an environment out of [empty] and [extend], so the representation
   (currently an association list) can be replaced later -- by a
   balanced map, say -- without touching a single line of the
   interpreter.

   Note that [extend] returns a *new* environment.  Nothing here
   mutates; an environment that has been captured by a closure can
   never be changed out from under it, which is exactly the property
   lexical scoping depends on. *)

type 'a t

(** The environment with no bindings at all. *)
val empty : 'a t

(** [extend name value env] is [env] plus the binding [name -> value].
    If [name] was already bound, the old binding is shadowed rather
    than overwritten, and it becomes visible again as soon as this
    environment goes out of scope. *)
val extend : string -> 'a -> 'a t -> 'a t

(** [lookup name env] is [Some value] when [name] is bound, and [None]
    otherwise.  The most recent binding for [name] wins. *)
val lookup : string -> 'a t -> 'a option

(** [is_bound name env] reports whether [name] has a binding. *)
val is_bound : string -> 'a t -> bool

(* ------------------------------------------------------------------ *)
(* Convenience operations built on top of the four above.  These are
   not required by the assignment; [of_list] is what the interpreter
   uses to install its predefined bindings (see the discussion of cin
   and cout in the docs folder), and [bindings] and [to_string] exist
   so that the evaluator's trace mode can print an environment. *)

(** [of_list pairs] extends [empty] with each pair, left to right, so a
    name appearing twice keeps its rightmost binding. *)
val of_list : (string * 'a) list -> 'a t

(** The visible bindings, innermost first.  Shadowed bindings are not
    included, since they cannot be observed through [lookup]. *)
val bindings : 'a t -> (string * 'a) list

(** [to_string string_of_value env] renders the visible bindings as
    ["[x = 10; y = 20]"]. *)
val to_string : ('a -> string) -> 'a t -> string
