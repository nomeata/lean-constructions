import Lean


open Lean Meta

/-
    constant_info ind_info = env.get(n);
    if (!ind_info.is_inductive())
        throw exception(sstream() << "error in '" << g_rec_on << "' generation, '" << n << "' is not an inductive datatype");
    name_generator ngen = mk_constructions_name_generator();
    local_ctx lctx;
    name rec_on_name(n, g_rec_on);
    constant_info rec_info = env.get(mk_rec_name(n));
    recursor_val  rec_val  = rec_info.to_recursor_val();
    buffer<expr> locals;
    expr rec_type = rec_info.get_type();
    while (is_pi(rec_type)) {
        expr local = lctx.mk_local_decl(ngen, binding_name(rec_type), binding_domain(rec_type), binding_info(rec_type));
        rec_type   = instantiate(binding_body(rec_type), local);
        locals.push_back(local);
    }

    // locals order
    //   As Cs minor_premises indices major-premise

    // new_locals order
    //   As Cs indices major-premise minor-premises
    buffer<expr> new_locals;
    unsigned num_indices  = rec_val.get_nindices();
    unsigned num_minors   = rec_val.get_nminors();
    unsigned AC_sz        = locals.size() - num_minors - num_indices - 1;
    for (unsigned i = 0; i < AC_sz; i++)
        new_locals.push_back(locals[i]);
    for (unsigned i = 0; i < num_indices + 1; i++)
        new_locals.push_back(locals[AC_sz + num_minors + i]);
    for (unsigned i = 0; i < num_minors; i++)
        new_locals.push_back(locals[AC_sz + i]);
    expr rec_on_type = lctx.mk_pi(new_locals, rec_type);

    levels ls = lparams_to_levels(rec_info.get_lparams());
    expr rec  = mk_constant(rec_info.get_name(), ls);
    expr rec_on_val = lctx.mk_lambda(new_locals, mk_app(rec, locals));

    environment new_env = env.add(mk_definition_inferring_unsafe(env, rec_on_name, rec_info.get_lparams(),
                                                                 rec_on_type, rec_on_val, reducibility_hints::mk_abbreviation()));
    new_env = set_reducible(new_env, rec_on_name, reducible_status::Reducible, true);
    new_env = add_aux_recursor(new_env, rec_on_name);
    return add_protected(new_env, rec_on_name);

-/

def mkRecOnVal (n : Name) (_iv : InductiveVal) : MetaM Expr := do
  -- let recOnInfo ← getConstInfoDefn (mkRecOnName n)
  -- return recOnInfo.value
  let .recInfo recInfo ← getConstInfo (mkRecName n)
    | throwError "{mkRecName n} not a recinfo"
  forallTelescope recInfo.type fun xs _ =>
    let e := .const recInfo.name (recInfo.levelParams.map (.param ·))
    let e := mkAppN e xs
    -- We reorder the parameters
    -- before: As Cs minor_premises indices major-premise
    -- fow:    As Cs indices major-premise minor-premises
    let AC_size := xs.size - recInfo.numMinors - recInfo.numIndices - 1
    let vs :=
      xs[:AC_size] ++
      xs[AC_size + recInfo.numMinors:AC_size + recInfo.numMinors + 1 + recInfo.numIndices] ++
      xs[AC_size:AC_size + recInfo.numMinors]
    mkLambdaFVars vs e

run_meta do
  let env ← getEnv
  for (n, ci) in env.constants do
    if ci.isInductive then
      let recOnName := mkRecOnName n
      unless env.contains  recOnName do
        -- happens on .below and ._impl inductives. how to filter them?
        -- logInfo m!"Missing {recOnName}"
        continue

      let newRecOnVal ← mkRecOnVal n ci.inductiveVal!
      let oldVal := (← getConstInfoDefn recOnName).value
      unless newRecOnVal == oldVal  do
        throwError m!"Mismatch for {n}:{indentExpr oldVal}\nvs{indentExpr newRecOnVal}"

  return ()
