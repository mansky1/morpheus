module Morpheus

open System.Collections.Generic
open Microsoft.Z3
open System.Reflection
open Microsoft.FSharp.Reflection

(* utility functions *)
let upd f x y z = if z = x then y else f z

let contains x l = List.exists (fun y -> y = x) l

let conmap f l = List.concat (Seq.map f l)

let rec remdups l = 
    match l with
    | [] -> []
    | x::xs -> if contains x xs then remdups xs else x :: remdups xs

let writer = System.IO.File.CreateText("output.txt")

(* module trans_syntax begin *)

(* General utility type for defining syntax with variables. *)
type literal<'data, 'mvar> = Inj of 'data | MVar of 'mvar

(* Expression pattern EPSubst (e, e') should match "an expression e with e' somewhere in it",
   allowing basic pattern-matching within a transformation; not currently implemented. *)
type expr_pattern<'mvar, 'expr> = EPInj of 'expr | EPSubst of 'mvar * 'expr | EPVar of 'mvar

(* Collecting free variables. *)
let lit_fv fv x = match x with Inj data -> fv data | MVar mv -> [mv]
let type_fv x = match x with Inj _ -> [] | MVar mv -> [mv]

let expr_pattern_fv expr_fv x = match x with EPInj e -> expr_fv e | EPSubst (x, e) -> x :: expr_fv e | EPVar v -> [v]

(* Actions are the atomic rewrites. *)
type action<'mvar, 'edge_type, 'pattern> = 
    | AAddNode of 'mvar * 'pattern * literal<('mvar * literal<'edge_type, 'mvar>) list, 'mvar>
    | ARemoveNode of 'mvar
    | ARelabelNode of 'mvar * 'pattern
    | AMoveEdge of 'mvar * (literal<'edge_type, 'mvar>) * 'mvar * 'mvar

let rec action_fv instr_fv a =
    match a with
    | AAddNode (n, p, el) -> match el with MVar v -> [v] | Inj el -> List.fold (fun vs (n', e) -> n' :: lit_fv (fun _ -> []) e @ vs) (n :: instr_fv p) el
    | ARemoveNode n -> [n]
    | ARelabelNode (n, p) -> n :: instr_fv p
    | AMoveEdge (n, e, n', n'') -> [n; n'; n''] @ lit_fv (fun _ -> []) e

(* Side conditions are CTL formulae on program graphs. *)
type side_cond<'mvar, 'pred> = 
 | SCTrue | SCPred of 'pred | SCAnd of side_cond<'mvar, 'pred> * side_cond<'mvar, 'pred> | SCNot of side_cond<'mvar, 'pred> 
 | SCAX of side_cond<'mvar, 'pred> | SCEX of side_cond<'mvar, 'pred> | SCAY of side_cond<'mvar, 'pred> | SCEY of side_cond<'mvar, 'pred>
 | SCAU of side_cond<'mvar, 'pred> * side_cond<'mvar, 'pred> | SCEU of side_cond<'mvar, 'pred> * side_cond<'mvar, 'pred>
 | SCAB of side_cond<'mvar, 'pred> * side_cond<'mvar, 'pred> | SCEB of side_cond<'mvar, 'pred> * side_cond<'mvar, 'pred>
 | SCEx of 'mvar * System.Type * side_cond<'mvar, 'pred>

let rec cond_fv pred_fv x = 
    match x with
    | SCTrue -> []
    | SCPred p -> pred_fv p
    | SCAnd (φ1, φ2) -> cond_fv pred_fv φ1 @ cond_fv pred_fv φ2
    | SCNot φ -> cond_fv pred_fv φ
    | SCAU (φ1, φ2) -> cond_fv pred_fv φ1 @ cond_fv pred_fv φ2
    | SCEU (φ1, φ2) -> cond_fv pred_fv φ1 @ cond_fv pred_fv φ2
    | SCAB (φ1, φ2) -> cond_fv pred_fv φ1 @ cond_fv pred_fv φ2
    | SCEB (φ1, φ2) -> cond_fv pred_fv φ1 @ cond_fv pred_fv φ2
    | SCAX φ -> cond_fv pred_fv φ
    | SCEX φ -> cond_fv pred_fv φ
    | SCAY φ -> cond_fv pred_fv φ
    | SCEY φ -> cond_fv pred_fv φ
    | SCEx (x, _, φ) -> List.filter (fun y -> y <> x) (cond_fv pred_fv φ)

(* CTL abbreviations *)
let SCFalse = SCNot SCTrue
let SCOr (φ1, φ2) = SCNot (SCAnd (SCNot φ1, SCNot φ2))
let SCImp (φ1, φ2) = SCNot (SCAnd (φ1, SCNot φ2))
let SCEF φ = SCEU (SCTrue, φ)
let SCAF φ = SCAU (SCTrue, φ)
let SCEG φ = SCNot (SCAF (SCNot φ))
let SCAG φ = SCNot (SCEF (SCNot φ))
let SCEP φ = SCEB (SCTrue, φ)
let SCAP φ = SCAB (SCTrue, φ)
let SCEH φ = SCNot (SCAP (SCNot φ))
let SCAH φ = SCNot (SCEP (SCNot φ))
let SCAll (x, ty, φ) = SCNot (SCEx (x, ty, SCNot φ))
let SCAW (φ, ψ) = SCNot (SCEU (SCNot ψ, (SCAnd (SCNot φ, SCNot ψ))))
let SCEW (φ, ψ) = SCOr (SCEU (φ, ψ), SCEG φ)

let rec SCAnds ps =
    match ps with
    [] -> SCTrue
    | p::ps -> SCAnd(p, SCAnds ps)

let rec SCOrs ps =
    match ps with
    [] -> SCFalse
    | p::ps -> SCOr(p, SCOrs ps)

let rec SCExs vs p =
    match vs with
    [] -> p
    | (v, ty) :: rest -> SCEx (v, ty, SCExs rest p)

let rec SCAlls vs p =
    match vs with
    [] -> p
    | (v, ty) :: rest -> SCAll (v, ty, SCAlls rest p)

(* Transformations are the top-level specs. *)
(* State conditions are paired with metavars indicating the node at which they're evaluated. *)
type transform<'mvar, 'edge_type, 'pattern, 'pred> = 
    | TA of action<'mvar, 'edge_type, 'pattern>
    | TSat of 'mvar * side_cond<'mvar, 'pred>
    | TNot of transform<'mvar, 'edge_type, 'pattern, 'pred>
    | TMinus of transform<'mvar, 'edge_type, 'pattern, 'pred> * transform<'mvar, 'edge_type, 'pattern, 'pred>
    | TExists of 'mvar * transform<'mvar, 'edge_type, 'pattern, 'pred>
    | TPlus of transform<'mvar, 'edge_type, 'pattern, 'pred> * transform<'mvar, 'edge_type, 'pattern, 'pred>
    | TSeq of transform<'mvar, 'edge_type, 'pattern, 'pred> * transform<'mvar, 'edge_type, 'pattern, 'pred>
    | TStar of transform<'mvar, 'edge_type, 'pattern, 'pred>

let rec TExist vs t =
    match vs with [] -> t | (v::morevs) -> TExists (v, TExist morevs t)

let TIf (a, n, p) = TSeq (TSat (n, p), TA a)

    
let rec trans_fv pred_fv instr_fv T =
    match T with
    | TA a -> action_fv instr_fv a
    | TSat (n, p) -> n :: cond_fv pred_fv p
    | TNot T -> trans_fv pred_fv instr_fv T
    | TMinus (T1, T2) -> trans_fv pred_fv instr_fv T1 @ trans_fv pred_fv instr_fv T2
    | TExists (x, T) -> List.filter (fun y -> y <> x) (trans_fv pred_fv instr_fv T)
    | TPlus (T1, T2) -> trans_fv pred_fv instr_fv T1 @ trans_fv pred_fv instr_fv T2
    | TSeq (T1, T2) -> trans_fv pred_fv instr_fv T1 @ trans_fv pred_fv instr_fv T2
    | TStar T -> trans_fv pred_fv instr_fv T

let rec TSeqs Ts =
    match Ts with
    [] -> TSat ("_dud", SCTrue)
    | [T] -> T
    | T::Ts -> TSeq (T, TSeqs Ts)
(* end *)

(* module trans_flowgraph begin *)

type edge<'node, 'edge_type> = 'node * 'node * 'edge_type

type flowgraph<'node, 'edge_type, 'instr when 'node : comparison and 'edge_type : comparison> = 
  { Nodes : Set<'node>; 
    Edges : Set<edge<'node, 'edge_type>>;
    Start : 'node; Label : Map<'node, 'instr> }

let size G = G.Nodes.Count

let out_edges G n = 
    Set.map (fun (x, y, z) -> (y, z)) (Set.filter (fun (x, y, z) -> x = n) G.Edges)

let print_graph G =
  Set.iter (fun i -> printfn "%d: %A\t %A" i (G.Label.TryFind i) (out_edges G i)) G.Nodes

let write_graph w G =
  Set.iter (fun i -> fprintfn w "%d: %A\t %A" i (G.Label.TryFind i) (out_edges G i)) G.Nodes

let next_node G t n =
    match Seq.tryFind (fun (a, b, c) -> a = n && c = t) G.Edges with Some (x, y, z) -> Some y | _ -> None

let in_edges G n = 
    Set.map (fun (x, y, z) -> (x, z)) (Set.filter (fun (x, y, z) -> y = n) G.Edges)
    
let used_vars fv G = Map.fold (fun r n i -> fv i @ r) [] G.Label

let increment (cfg:flowgraph<int, 't, 'instr>) n = {
    Nodes = Set.map (fun x -> x + n) cfg.Nodes;
    Edges = Set.map (fun (a, b, t) -> (a + n, b + n, t)) cfg.Edges;
    Start = cfg.Start + n;
    Label = new Map<int, 'instr>(seq {for KeyValue(k, v) in cfg.Label -> (k + n, v)}) }

(* end *)

(* module ctl_check begin *)

let _opts = new Dictionary<string, string>()
_opts.Add("MODEL","true")
let context = new Context(_opts)
let both = context.MkAnd()
let solver = context.MkSolver()
ignore(solver.Check())
let empty_model = solver.Model
solver.Reset()

let mkvar sort (name:string) = context.MkConst(name, sort)

let rec cross (m:Map<string, Set<int>>) = Map.fold (fun r t l -> conmap (fun s -> List.map (fun m -> Map.add t s m) r) l) [(new Map<string, int>(Seq.empty))] m

(* Generics by reflection. By inspecting the instruction type, we can build Z3 datatypes and 
   convert instructions and patterns into them. *)
let mutable type_table:Dictionary<System.Type, Sort> = null

(* Make a Z3 sort corresponding to a datatype. *)
(* Works only for non-recursive or directly recursive union types (no mutual recursion). *)
(* Now assuming tuples are always edge pieces. *)
let rec mk_z3_sort (t:System.Type) =
    if t.Name = "literal`2" then mk_z3_sort (t.GenericTypeArguments.[0])
    elif t.Name = "expr_pattern`2" then mk_z3_sort (t.GenericTypeArguments.[1])
    elif type_table.ContainsKey(t) then type_table.[t]
    elif t.Name = "FSharpList`1" then context.MkSetSort(mk_z3_sort t.GenericTypeArguments.[0]) :> Sort
    elif t.Name = "Tuple`2" then
        let ty = context.MkTupleSort(context.MkSymbol("edge"), [|context.MkSymbol("node"); context.MkSymbol("type")|], [|context.MkIntSort(); mk_z3_sort t.GenericTypeArguments.[1]|])
        type_table.[t] <- ty
        ty :> Sort
    else let ty = context.MkDatatypeSort(t.Name,[|for c in FSharpType.GetUnionCases(t) -> context.MkConstructor(c.Name, "is_" + c.Name, 
        [|for f in c.GetFields() -> f.Name|], 
        [|for f in c.GetFields() -> let t' = f.PropertyType in if t = t' then null else mk_z3_sort t'|], 
        [|for f in c.GetFields() -> 0u|])|])
         type_table.[t] <- ty
         ty :> Sort

let edge_sort t = context.MkTupleSort(context.MkSymbol("edge"), [|context.MkSymbol("node"); context.MkSymbol("type")|], [|context.MkIntSort(); mk_z3_sort t|])

(* Convert a program pattern to a Z3 datatype, assuming strings represent metavariables. *)
let rec convert_p p = (*memoize?*)
    let t = p.GetType()
    if t = typeof<string> then mkvar (mk_z3_sort typeof<string>) (p.ToString())
    elif t = typeof<int> then context.MkInt(p.ToString()) :> Expr
    else
        let c, args = FSharpValue.GetUnionFields(p, t)
        if c.DeclaringType.Name = "literal`2" then 
            if c.Name = "MVar" then mkvar (mk_z3_sort (t.GenericTypeArguments.[0])) (args.[0].ToString()) else convert_p args.[0]
        elif c.DeclaringType.Name = "expr_pattern`2" then 
            if c.Name = "EPInj" then convert_p (args.[0])
            elif c.Name = "EPVar" then mkvar (mk_z3_sort (t.GenericTypeArguments.[1])) (args.[0].ToString())
            else null (* need code for EPSubst - match a function? *)
        else
            let ty = mk_z3_sort (c.DeclaringType) :?> DatatypeSort
            let i = Array.findIndex (fun c' -> c' = c) (FSharpType.GetUnionCases t)
            context.MkApp(ty.Constructors.[i], [|for x in args -> convert_p x|])

let get_const (enum_sort:EnumSort) name =
    context.MkApp(Array.find (fun (e:FuncDecl) -> e.Name.ToString() = name) enum_sort.ConstDecls)
    
(* Convert a program object to a Z3 datatype, assuming strings represent concrete variables. *)
let rec convert_i p =
    let t = p.GetType()
    if t = typeof<string> then get_const (mk_z3_sort typeof<string> :?> EnumSort) (p.ToString())
    elif t = typeof<int> then context.MkInt(p.ToString()) :> Expr
    else
        let c, args = FSharpValue.GetUnionFields(p, t)
        let ty = mk_z3_sort (c.DeclaringType) :?> DatatypeSort
        let i = Array.findIndex (fun c' -> c' = c) (FSharpType.GetUnionCases t)
        context.MkApp(ty.Constructors.[i], [|for x in args -> convert_i x|])

(* Recover an F# datatype from a Z3 datatype. *)
let rec strip (t:System.Type) =
    if t.Name = "literal`2" then strip (t.GenericTypeArguments.[0])
    elif t.Name = "expr_pattern`2" then strip (t.GenericTypeArguments.[1])
    elif t.IsGenericType then t.GetGenericTypeDefinition().MakeGenericType([|for p in t.GenericTypeArguments -> strip p|])
    else t

let rec recover_i (e:Expr) =
    let ty = (Seq.head (Seq.filter (fun (KeyValue(_, s)) -> s = e.Sort) type_table)).Key
    let t = strip ty
    if t = typeof<string> then e.FuncDecl.Name.ToString() :> obj
    elif t = typeof<int> then (e :?> IntNum).Int :> obj
    elif t.Name = "Tuple`2" then
        let vals = [|for a in e.Args -> recover_i a|]
        FSharpValue.MakeTuple(vals, FSharpType.MakeTupleType([|for v in vals -> v.GetType()|]))
    else
        let c = Array.find (fun (x:UnionCaseInfo) -> x.Name = e.FuncDecl.Name.ToString()) (FSharpType.GetUnionCases(t))
        FSharpValue.MakeUnion(c, [|for a in e.Args -> recover_i a|])
        
(* Offload substitution to Z3. *)
let subst (s:Model) p =
    let pat = convert_p p
    let v = s.Eval(pat)
    if v.IsArray then let f = s.FuncInterp(pat.FuncDecl) in [|for e in f.Entries -> recover_i (e.Args.[0])|] :> obj
    else recover_i v

(* Find strings in recursive datatypes. *)
let rec freevars (p:obj) =
    let t = p.GetType()
    if t = typeof<string> then [p :?> string]
    elif FSharpType.IsUnion(t) then Array.fold (fun r o -> r @ freevars o) [] (snd (FSharpValue.GetUnionFields(p, t)))
    else []

(* Memoization helps a lot. *)
let rec paths_or caches mk_pred cfgs p0 p n m = 
    let (_, cache:Dictionary<_,_>, _, _, _) = caches
    if cache.ContainsKey((p0, p, n, m)) then cache.[(p0, p, n, m)]
    else 
    let res = 
        if n <= 0 then satis caches mk_pred cfgs m p else context.MkOr(paths_or caches mk_pred cfgs p0 p (n - 1) m, context.MkAnd(satis caches mk_pred cfgs m p0, 
            context.MkOr(List.toArray (List.map (fun m' -> paths_or caches mk_pred cfgs p0 p (n - 1) m') (List.filter (fun m' -> m' <> m) (Set.toList (Set.map fst (out_edges cfgs m))))))))
    cache.[(p0, p, n, m)] <- res
    res
and rpaths_and caches mk_pred cfgs p0 p n m = 
    let (_, _, _, _, cache:Dictionary<_,_>) = caches
    if cache.ContainsKey((p0, p, n, m)) then cache.[(p0, p, n, m)]
    else
    let res =
        if n <= 0 then satis caches mk_pred cfgs m p
        else let prevs = List.filter (fun m' -> m' <> m) (Set.toList (Set.map fst (in_edges cfgs m)))
             context.MkOr(rpaths_and caches mk_pred cfgs p0 p (n - 1) m,
             if prevs = [] then context.MkBool(false) else
             context.MkAnd(satis caches mk_pred cfgs m p0,
                           context.MkAnd(List.toArray (List.map (fun m' -> rpaths_and caches mk_pred cfgs p0 p (n - 1) m') prevs))))
    cache.[(p0, p, n, m)] <- res
    res
and rpaths_or caches mk_pred cfgs p0 p n m = 
    let (_, _, cache:Dictionary<_,_>, _, _) = caches
    if cache.ContainsKey((p0, p, n, m)) then cache.[(p0, p, n, m)]
    else
    let res =
        if n <= 0 then satis caches mk_pred cfgs m p else context.MkOr(rpaths_or caches mk_pred cfgs p0 p (n - 1) m, context.MkAnd(satis caches mk_pred cfgs m p0,
            context.MkOr(List.toArray (List.map (fun m' -> rpaths_or caches mk_pred cfgs p0 p (n - 1) m') (List.filter (fun m' -> m' <> m) (Set.toList (Set.map fst (in_edges cfgs m))))))))
    cache.[(p0, p, n, m)] <- res
    res
and paths_and caches mk_pred cfgs p0 p n m = 
    let (_, _, _, cache:Dictionary<_,_>, _) = caches
    if cache.ContainsKey((p0, p, n, m)) then cache.[(p0, p, n, m)]
    else
    let res =
        if n <= 0 then satis caches mk_pred cfgs m p
        else let nexts = List.filter (fun m' -> m' <> m) (Set.toList (Set.map fst (out_edges cfgs m)))
             context.MkOr(paths_and caches mk_pred cfgs p0 p (n - 1) m,
             if nexts = [] then context.MkBool(false) else
             context.MkAnd(satis caches mk_pred cfgs m p0,
                           context.MkAnd(List.toArray (List.map (fun m' -> paths_and caches mk_pred cfgs p0 p (n - 1) m') nexts))))
    cache.[(p0, p, n, m)] <- res
    res
and satis caches mk_pred cfgs m p = 
    let (cache:Dictionary<_,_>, _, _, _, _) = caches
    if cache.ContainsKey((m, p)) then cache.[(m, p)]
    else 
    let res = 
        match p with
        | SCPred p -> let (e:BoolExpr) = mk_pred cfgs m p in e.Simplify() :?> BoolExpr (* unnecessary and might slow it down, but allows for cleaner debug output *)
        | SCTrue -> context.MkBool(true)
        | SCNot p -> context.MkNot(satis caches mk_pred cfgs m p)
        | SCAnd (p1, p2) -> context.MkAnd(satis caches mk_pred cfgs m p1, satis caches mk_pred cfgs m p2)
        | SCEx (x:string, ty, p) -> context.MkExists([|context.MkConst(x, mk_z3_sort ty)|], satis caches mk_pred cfgs m p) :> BoolExpr (* need a sort for x *)
        | SCAX p -> let nexts = List.filter (fun m' -> m' <> m) (Set.toList (Set.map fst (out_edges cfgs m)))
                    context.MkAnd(context.MkAnd(List.toArray (List.map (fun n -> satis caches mk_pred cfgs n p) nexts)), context.MkBool(nexts <> []))
        | SCEX p -> let nexts = List.filter (fun m' -> m' <> m) (Set.toList (Set.map fst (out_edges cfgs m)))
                    context.MkOr(List.toArray (List.map (fun n -> satis caches mk_pred cfgs n p) nexts))
        | SCAY p -> let prevs = List.filter (fun m' -> m' <> m) (Set.toList (Set.map fst (in_edges cfgs m)))
                    context.MkAnd(context.MkAnd(List.toArray (List.map (fun n -> satis caches mk_pred cfgs n p) prevs)), context.MkBool(prevs <> []))
        | SCEY p -> let prevs = List.filter (fun m' -> m' <> m) (Set.toList (Set.map fst (in_edges cfgs m)))
                    context.MkOr(List.toArray (List.map (fun n -> satis caches mk_pred cfgs n p) prevs))
        | SCAU (p1, p2) -> paths_and caches mk_pred cfgs p1 p2 (size cfgs) m
        | SCEU (p1, p2) -> paths_or caches mk_pred cfgs p1 p2 (size cfgs) m
        | SCAB (p1, p2) -> rpaths_and caches mk_pred cfgs p1 p2 (size cfgs) m
        | SCEB (p1, p2) -> rpaths_or caches mk_pred cfgs p1 p2 (size cfgs) m
    cache.[(m, p)] <- res
    res

let mk_exprs (m:Model) = 
    [|for decl in m.ConstDecls ->
      if decl.Range.SortKind = Z3_sort_kind.Z3_ARRAY_SORT then
        let f = m.FuncInterp(decl) in context.MkEq(context.MkConst(decl),
          Array.fold (fun s (e:FuncInterp.Entry) -> context.MkSetAdd(s, e.Args.[0])) (context.MkEmptySet((decl.Range :?> ArraySort).Domain)) f.Entries)
      else context.MkEq(context.MkConst(decl), m.ConstInterp(decl))|]

let mk_conds (m:Model) vars = 
    [|for decl in Array.filter (fun (d:FuncDecl) -> contains (d.Name.ToString()) vars) m.ConstDecls -> 
      if decl.Range.SortKind = Z3_sort_kind.Z3_ARRAY_SORT then
        let f = m.FuncInterp(decl) in context.MkEq(context.MkConst(decl),
          Array.fold (fun s (e:FuncInterp.Entry) -> context.MkSetAdd(s, e.Args.[0])) (context.MkEmptySet((decl.Range :?> ArraySort).Domain)) f.Entries)
      else context.MkEq(context.MkConst(decl), m.ConstInterp(decl))|]

(* memoization courtesy Don Syme http://blogs.msdn.com/b/dsyme/archive/2007/05/31/a-sample-of-the-memoization-pattern-in-f.aspx *)
let memo_satis mk_pred cfgs n p = 
    let scache = Dictionary<_,_>()
    let pbcache = Dictionary<_,_>()
    let rfcache = Dictionary<_,_>()
    let pacache = Dictionary<_,_>()
    let racache = Dictionary<_,_>()
    satis (scache, pbcache, rfcache, pacache, racache) mk_pred cfgs n p
    
             
let rec get_all_models vars n acc = if n <= 0 then acc else (   
    (*printfn "Invoking Z3..."*)
    stdout.Flush()
    let response = solver.Check() 
    (*printfn "Z3 returned %s" (response.ToString())*)
    stdout.Flush()
    if response = Status.SATISFIABLE 
    then 
(*        fprintfn writer "\n%A\n" solver.Model *)
        let acc' = solver.Model :: acc
        solver.Assert(context.MkNot(context.MkAnd(mk_conds solver.Model vars)))
        get_all_models vars (n - 1) acc'
    else acc)

let keys m = Map.fold (fun r k v -> k :: r) [] m

let check_enum (sort:EnumSort) (var:string) name =
    let tester = Array.find (fun (t:FuncDecl) -> t.Name.ToString() = "is_" + name) sort.TesterDecls
    context.MkApp(tester, mkvar sort var) :?> BoolExpr

(* make fresh variables *)
let rec next_fresh vs n = if List.exists (fun v -> "_fresh" + n.ToString() = v) vs then next_fresh vs (n + 1) else n
let rec make_fresh_aux names (map, used) n =
    match names with
    | [] -> (map, used)
    | f::rest -> let n' = next_fresh used n in let v' = "_fresh" + n'.ToString() in make_fresh_aux rest (Map.add f v' map, v'::used) (n' + 1)
let make_fresh used names = make_fresh_aux names (new Map<string, string>([]), used) 0

(* The main interface to the SMT solver. *)
let get_models mk_pred pred_fv instr_fv fresh tau cfgs p n =
    let (fresh_map, vars) = make_fresh (used_vars instr_fv cfgs) fresh
    let var_sort = context.MkEnumSort("var", if vars <> [] then List.toArray vars else [|"dud"|])
    type_table <- Dictionary<System.Type, Sort>()
    type_table.[typeof<string>] <- var_sort
    type_table.[typeof<int>] <- context.MkIntSort()
    solver.Reset()
    solver.Assert([|for KeyValue(k, v) in fresh_map -> check_enum var_sort k v|])
    solver.Assert(mk_exprs tau)
    solver.Assert(memo_satis mk_pred cfgs n p)
    (*fprintfn writer "%A" (solver.Assertions)
    fprintfn writer "%A" (solver.Assertions.[0].Simplify())
    writer.Flush()*)
    get_all_models (cond_fv pred_fv p) 200 [] (* set the maximum number of models returned *)

(* end *)

(* module trans_semantics begin *)

let node_subst cfgs (s:Model) (n:string) = 
  try
  Some ((s.ConstInterp(context.MkIntConst(n)) :?> IntNum).Int)
  with e -> None

let lit_subst dsubst (s:Model) (l:literal<'data, 'mvar>) =
  match l with
  | Inj d -> dsubst s d
  | MVar v -> subst s l :?> 'data

let rec update_map m l = 
    match l with
    | [] -> m
    | ((x, y) :: rest) -> update_map (Map.add x y m) rest

(* This forces nodes to be ints. We could parameterize for generality. *)
let fresh_nodes l n = [Set.maxElement l + 1 .. Set.maxElement l + n]

let subst_list subst s pl = List.fold (fun r p -> match (r, subst s p) with (Some l, Some i) -> Some (l @ [i]) | _ -> None) (Some []) pl

let action_sf type_subst set_subst subst A s (G:flowgraph<int, 'edge_type, 'instr>) = 
    match A with
    | AAddNode (n, l, el) -> 
        match subst s l with 
        | Some i ->
             let u = (fresh_nodes G.Nodes 1).Head
             (*if node_subst G s n = Some u then*)
             let (el' : Set<int * int * 'edge_type> option) = match el with
                       | MVar v -> Some (Set.map (fun (m, d) -> (u, m, d)) (Set.ofArray (set_subst s el)))
                       | Inj el -> List.fold (fun (es : Set<int * int * 'edge_type> option) (m, d) -> match (es, lit_subst type_subst s d, node_subst G s m) with
                                                               | (Some es, t, Some v) -> Some (Set.add (u, v, t) es)
                                                               | _ -> None) (Some Set.empty) el
             match el' with
             | Some es -> Some {G with Nodes = Set.add u G.Nodes; Edges = Set.union G.Edges es; Label = Map.add u i G.Label}
             | None -> None
             (*else None*)
        | _ -> None
    | ARemoveNode n -> 
        match node_subst G s n with
        | Some u -> if Set.contains u G.Nodes then Some {G with Nodes = Set.remove u G.Nodes; Edges = Set.filter (fun (u', v, t) -> u' <> u) G.Edges}
                    else None
        | _ -> None
    | ARelabelNode (n, l) ->
        match (node_subst G s n, subst s l) with 
        | (Some u, Some i) -> Some {G with Label = Map.add u i G.Label}
        | _ -> None
    | AMoveEdge (n, e, m1, m2) -> 
        match (node_subst G s n, node_subst G s m1, node_subst G s m2, lit_subst type_subst s e) with
        | (Some u, Some v1, Some v2, ty) -> 
            if not (Set.exists (fun x -> x = u) G.Nodes) then None 
            elif not (Set.contains (u, v1, ty) G.Edges) then None
            else (if Set.exists (fun x -> x = v1) G.Nodes 
                  then Some {G with Edges = Set.add (u, v2, ty) (Set.filter (fun e -> e <> (u, v1, ty)) G.Edges)} else None)
        | _ -> None

let rec action_list_sf type_subst set_subst subst al s cfgs = 
    match al with
    | [] -> Some cfgs
    | A :: rest -> 
        match action_sf type_subst set_subst subst A s cfgs with None -> None | Some cfgs' -> action_list_sf type_subst set_subst subst rest s cfgs'

(* Can we do renaming via Z3? *)
let replace x y v = if x = v then y else v

let rename_lit rn x y l = match l with MVar v -> MVar (replace x y v) | Inj d -> Inj (rn x y d)

let rename_action rename_edge rename_instr x y a =
    match a with
    | AAddNode (n, p, el) -> AAddNode (replace x y n, rename_instr x y p,
        match el with MVar v -> MVar (replace x y v) | Inj el -> Inj (List.fold (fun l (m, e) -> l @ [(replace x y m, rename_lit rename_edge x y e)]) [] el))
    | ARemoveNode n -> ARemoveNode (replace x y n)
    | ARelabelNode (n, p) -> ARelabelNode (replace x y n, rename_instr x y p)
    | AMoveEdge (n, e, m1, m2) -> AMoveEdge (replace x y n, rename_lit rename_edge x y e, replace x y m1, replace x y m2)

let rec rename_cond rename_pred x y p =
    match p with
    | SCTrue -> SCTrue
    | SCPred p -> SCPred (rename_pred x y p)
    | SCAnd (p1, p2) -> SCAnd (rename_cond rename_pred x y p1, rename_cond rename_pred x y p2)
    | SCNot p -> SCNot (rename_cond rename_pred x y p)
    | SCAU (p1, p2) -> SCAU (rename_cond rename_pred x y p1, rename_cond rename_pred x y p2)
    | SCEU (p1, p2) -> SCEU (rename_cond rename_pred x y p1, rename_cond rename_pred x y p2)
    | SCAB (p1, p2) -> SCAB (rename_cond rename_pred x y p1, rename_cond rename_pred x y p2)
    | SCEB (p1, p2) -> SCEB (rename_cond rename_pred x y p1, rename_cond rename_pred x y p2)
    | SCAX p -> SCAX (rename_cond rename_pred x y p)
    | SCEX p -> SCEX (rename_cond rename_pred x y p)
    | SCAY p -> SCAY (rename_cond rename_pred x y p)
    | SCEY p -> SCEY (rename_cond rename_pred x y p)
    | SCEx (v, t, p) -> if v = x then SCEx (v, t, p) else SCEx (v, t, rename_cond rename_pred x y p)
    
let rec rename rename_edge rename_instr rename_pred x y T =
    match T with
    | TA a -> TA (rename_action rename_edge rename_instr x y a)
    | TSat (n, p) -> TSat (replace x y n, rename_cond rename_pred x y p)
    | TNot T -> TNot (rename rename_edge rename_instr rename_pred x y T)
    | TMinus (T1, T2) -> TMinus (rename rename_edge rename_instr rename_pred x y T1, rename rename_edge rename_instr rename_pred x y T2)
    | TExists (v, T) -> if v = x then TExists (v, T) else TExists (v, rename rename_edge rename_instr rename_pred x y T)
    | TPlus (T1, T2) -> TPlus (rename rename_edge rename_instr rename_pred x y T1, rename rename_edge rename_instr rename_pred x y T2)
    | TSeq (T1, T2) -> TSeq (rename rename_edge rename_instr rename_pred x y T1, rename rename_edge rename_instr rename_pred x y T2)
    | TStar T -> TStar (rename rename_edge rename_instr rename_pred x y T)

let add_node s (n:string) (m:int) =
    solver.Reset()
    solver.Assert(mk_exprs s)
    solver.Assert(context.MkEq(context.MkIntConst(n), context.MkInt(m)))
    ignore(solver.Check())
    solver.Model

let mutable fresh_index = 0

(* Take in one GCFG, produce a list. *)
let rec trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T tau G = 
    match T with
    | TA a -> match action_sf type_subst set_subst subst a tau G with Some G' -> [(G', tau)] | None -> []
    | TSat (n, p) -> match node_subst G tau n with
        | Some n' -> List.map (fun t -> (G, t)) (get_models mk_pred pred_fv instr_fv [](*fresh*) tau G p n')
        | None -> List.concat (List.map (fun m -> List.map (fun t -> (G, t)) (get_models mk_pred pred_fv instr_fv [](*fresh*) (add_node tau n m) G p m)) (Set.toList G.Nodes))
    | TNot T -> if trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T tau G = [] then [(G, tau)] else []
    | TMinus (T1, T2) -> let gs = trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T2 tau G in
                         List.filter (fun r -> List.forall (fun g -> g <> r) gs) (trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T1 tau G)
    | TExists (x, T) -> let y = "_bound" + fresh_index.ToString() + "_" + x
                        fresh_index <- fresh_index + 1
                        let T' = (rename rename_edge rename_instr rename_pred x y T)
                        trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T' tau G
    | TPlus (T1, T2) -> remdups (trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T1 tau G @
                                 trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T2 tau G)
    | TSeq (T1, T2) -> let r = (trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T1 tau G)
                       remdups (conmap (fun (G', t') -> trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T2 t' G') (List.toSeq r))
    | TStar T -> let r = List.filter (fun r -> r <> (G, tau)) (remdups (trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst T tau G))
                 remdups ((G, tau) :: List.concat (List.map (fun (r, t) -> trans_sf mk_pred pred_fv instr_fv pattern_fv rename_edge rename_instr rename_pred type_subst set_subst subst (TStar T) t r) r))
    
(* very simple sample language *)
(* Instruction patterns and substitution. *)
type edge_type = Seq | Branch

type instr = Skip | Assign of string * string

let pattern_fv i = 
    match i with
    | Skip -> []
    | Assign (x, y) -> [x; y]

(* generic atomic predicates *)
type int_expr = Intv of string | Intc of int | Plus of int_expr * int_expr | Times of int_expr * int_expr
let rec int_expr_to_z3 i = 
    match i with
    | Intv v -> context.MkIntConst(v) :> ArithExpr
    | Intc c -> context.MkInt(c) :> ArithExpr
    | Plus (i, j) -> context.MkAdd(int_expr_to_z3 i, int_expr_to_z3 j)
    | Times (i, j) -> context.MkMul(int_expr_to_z3 i, int_expr_to_z3 j)

type simple_pred<'edge_type, 'instr> when 'edge_type : comparison = 
    | Node of string | Stmt of 'instr | AtStart
    | In of string * literal<'edge_type, string>
    | Out of string * literal<'edge_type, string>
    | Is of int_expr * int_expr | IsNot of int_expr * int_expr
    | Out_edges of literal<Set<int * 'edge_type>, string>
    | Fresh of string | PEq of string * string

let rec rn_int_expr x y e =
    match e with
    | Intv v -> Intv (replace x y v)
    | Intc i -> Intc i
    | Plus (e1, e2) -> Plus (rn_int_expr x y e1, rn_int_expr x y e2)
    | Times (e1, e2) -> Times (rn_int_expr x y e1, rn_int_expr x y e2)

let rn_pred rn_edge rn_instr x y p =
    match p with
    | Node n -> Node (replace x y n)
    | Stmt i -> Stmt (rn_instr x y i)
    | In (n, e) -> In (replace x y n, rename_lit rn_edge x y e)
    | Out (n, e) -> Out (replace x y n, rename_lit rn_edge x y e)
    | Is (e1, e2) -> Is (rn_int_expr x y e1, rn_int_expr x y e2)
    | IsNot (e1, e2) -> IsNot (rn_int_expr x y e1, rn_int_expr x y e2)
    | AtStart -> AtStart
    | Out_edges s -> Out_edges (rename_lit (fun _ _ c -> c) x y s)
    | Fresh n -> Fresh (replace x y n)
    | PEq (a, b) -> PEq (replace x y a, replace x y b)

let node n = SCPred (Node n)
let stmt i = SCPred (Stmt i)
let out n ty = SCPred (Out (n, ty))
let start = SCPred AtStart

(* The generic approach to predicate semantics. *)
let add_stmt_case cfgs p s =
    match Map.tryFind s cfgs.Label with
    | Some i -> context.MkEq(convert_p p, convert_i i)
    | None -> context.MkFalse()

let mk_simple_pred2 (cfgs:flowgraph<'node, 'edge_type, 'instr>) (m:int) p = 
    match p with
    | Node n -> context.MkEq(context.MkIntConst(n), context.MkInt(m))
    | Stmt p -> add_stmt_case cfgs p m
    | In (n, ty) -> Set.fold (fun e ((m':int), t) -> context.MkOr(e, context.MkAnd(context.MkEq(context.MkIntConst(n), context.MkInt(m')), context.MkEq(convert_p ty, convert_i t)))) (context.MkBool(false)) (in_edges cfgs m)
    | Out (n, ty) -> Set.fold (fun e ((m':int), t) -> context.MkOr(e, context.MkAnd(context.MkEq(context.MkIntConst(n), context.MkInt(m')), context.MkEq(convert_p ty, convert_i t)))) (context.MkBool(false)) (out_edges cfgs m)
    | Is (i, j) -> context.MkEq(int_expr_to_z3 i, int_expr_to_z3 j)
    | IsNot (i, j) -> context.MkNot(context.MkEq(int_expr_to_z3 i, int_expr_to_z3 j))
    | AtStart -> context.MkEq(context.MkInt(m), context.MkInt(cfgs.Start))
    | Out_edges s ->
        let tuple_sort = edge_sort typeof<'edge_type>
        match s with         
        | MVar s -> context.MkEq(context.MkArrayConst(s, tuple_sort, context.MkBoolSort()),
        Set.fold (fun e ((m':int), t) -> context.MkSetAdd(e, context.MkApp(tuple_sort.MkDecl, [|context.MkInt(m') :> Expr; convert_i t|]))) (context.MkEmptySet(tuple_sort)) (out_edges cfgs m))
        | Inj vals -> if vals = out_edges cfgs m then context.MkTrue() else context.MkFalse()
    | Fresh n -> context.MkEq(context.MkIntConst(n), context.MkInt((fresh_nodes cfgs.Nodes 1).Head))
    | PEq (a, b) -> context.MkEq(convert_p a, convert_p b)

let type_subst s (x:'a) = 
    let r = subst s x
    if r.GetType() = typeof<'a> then Some (r :?> 'a) else None

let set l = Set.ofList l

let simple_cfg1 = { Nodes = set [1; 2; 3]; Edges = set [(1, 2, Seq); (2, 3, Seq)]; Start = 1;
                    Label = new Map<int, instr>(List.toSeq [(1, Skip); (2, Skip); (3, Skip)]) }
let simple_cfg2 = { Nodes = set [4; 5; 6; 7]; Edges = set [(4, 5, Seq); (5, 6, Seq); (5, 7, Branch); (6, 7, Seq)]; Start = 4;
                    Label = new Map<int, instr>(List.toSeq [(4, Skip); (5, Assign ("x", "y")); (6, Assign ("a", "b")); (7, Skip)]) }

(* end *)