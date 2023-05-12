open Datatypes
open EAst
open Kernames
open List0
open Monad_utils

module GlobalContextMap =
 struct
  type t = { global_decls : global_declarations;
             map : global_decl EnvMap.EnvMap.t }

  (** val map : t -> global_decl EnvMap.EnvMap.t **)

  let map t0 =
    t0.map

  (** val lookup_env : t -> kername -> global_decl option **)

  let lookup_env _UU03a3_ kn =
    EnvMap.EnvMap.lookup kn _UU03a3_.map

  (** val lookup_minductive : t -> kername -> mutual_inductive_body option **)

  let lookup_minductive _UU03a3_ kn =
    bind (Obj.magic option_monad) (Obj.magic lookup_env _UU03a3_ kn)
      (fun decl ->
      match decl with
      | ConstantDecl _ -> None
      | InductiveDecl mdecl -> ret (Obj.magic option_monad) mdecl)

  (** val lookup_inductive :
      t -> inductive -> (mutual_inductive_body * one_inductive_body) option **)

  let lookup_inductive _UU03a3_ kn =
    bind (Obj.magic option_monad)
      (Obj.magic lookup_minductive _UU03a3_ kn.inductive_mind) (fun mdecl ->
      bind (Obj.magic option_monad)
        (nth_error (Obj.magic mdecl.ind_bodies) kn.inductive_ind)
        (fun idecl -> ret (Obj.magic option_monad) (mdecl, idecl)))

  (** val inductive_isprop_and_pars :
      t -> inductive -> (bool * nat) option **)

  let inductive_isprop_and_pars _UU03a3_ ind =
    bind (Obj.magic option_monad) (Obj.magic lookup_inductive _UU03a3_ ind)
      (fun x ->
      let (mdecl, idecl) = x in
      ret (Obj.magic option_monad) (idecl.ind_propositional, mdecl.ind_npars))

  (** val make : global_declarations -> t **)

  let make g =
    { global_decls = g; map = (EnvMap.EnvMap.of_global_env g) }
 end
