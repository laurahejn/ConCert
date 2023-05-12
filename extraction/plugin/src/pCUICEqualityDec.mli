open All_Forall
open BasicAst
open Datatypes
open Kernames
open List0
open PCUICAst
open PCUICEquality
open Universes0
open Config0
open UGraph0

val compare_universe_variance :
  (Universe.t -> Universe.t -> bool) -> (Universe.t -> Universe.t -> bool) ->
  Variance.t -> Level.t -> Level.t -> bool

val compare_universe_instance :
  (Universe.t -> Universe.t -> bool) -> Level.t list -> Level.t list -> bool

val compare_universe_instance_variance :
  (Universe.t -> Universe.t -> bool) -> (Universe.t -> Universe.t -> bool) ->
  Variance.t list -> Level.t list -> Level.t list -> bool

val compare_global_instance :
  PCUICEnvironment.global_env -> (Universe.t -> Universe.t -> bool) ->
  (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> Level.t
  list -> Level.t list -> bool

val conv_pb_relb :
  checker_flags -> universes_graph -> conv_pb -> Universe.t -> Universe.t ->
  bool
