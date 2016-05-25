(* An LLVM-like target language. *)
module MiniLLVM

open Microsoft.Z3
open Morpheus

type LLVM_type = Int_ty | Pointer_ty of LLVM_type
type LLVM_expr<'var, 'con> = Local of 'var | CInt of 'con | CPointer of 'con | CUndef | Global of string
type LLVM_op = Add | Sub | Mul
type LLVM_cmp = Eq | Ne | Sgt | Sge | Slt | Sle

(* TODO: better concrete syntax *)
type LLVM_instr<'var, 'ty, 'expr, 'opr, 'cmp> = 
 | Assign of 'var * 'opr * 'ty * 'expr * 'expr | ICmp of 'var * 'cmp * 'ty * 'expr * 'expr
 | Br_i1 of 'expr (* conditional branch *) | Br_label (* unconditional *) 
 | Alloca of 'var * 'ty | Load of 'var * 'ty * 'expr | Store of 'ty * 'expr * 'ty * 'expr 
 | Cmpxchg of 'var * 'ty * 'expr * 'ty * 'expr * 'ty * 'expr 
(* | Call of 'var * 'ty * list<'expr> | Ret of 'ty * 'expr*) | IsPointer of 'expr

(*type LLVM_decl = Global_Decl of string * LLVM_const*)

type LLVM_edge_type = Seq | True | False (*| Proc_call | Proc_ret*)

type pattern<'mvar> = literal<LLVM_instr<'mvar, literal<LLVM_type, 'mvar>, literal<LLVM_expr<'mvar, literal<int, 'mvar>>, 'mvar>, 
     literal<LLVM_op, 'mvar>, literal<LLVM_cmp, 'mvar>>, 'mvar>

let rn_id x y z = z

let rn_expr x y e =
    match e with
    | Local v -> Local (replace x y v)
    | CInt i -> CInt (rename_lit rn_id x y i)
    | CPointer p -> CPointer (rename_lit rn_id x y p)
    | CUndef -> CUndef
    | Global v -> Global (replace x y v)

let rn_instr x y i =
    match i with
    | Assign (v, op, t, e1, e2) -> Assign (replace x y v, rename_lit rn_id x y op, rename_lit rn_id x y t, rename_lit rn_expr x y e1, rename_lit rn_expr x y e2)
    | ICmp (v, op, t, e1, e2) -> ICmp (replace x y v, rename_lit rn_id x y op, rename_lit rn_id x y t, rename_lit rn_expr x y e1, rename_lit rn_expr x y e2)
    | Br_i1 e -> Br_i1 (rename_lit rn_expr x y e)
    | Br_label -> Br_label
    | Alloca (v, t) -> Alloca (replace x y v, rename_lit rn_id x y t)
    | Load (v, t, e) -> Load (replace x y v, rename_lit rn_id x y t, rename_lit rn_expr x y e)
    | Store (t1, e1, t2, e2) -> Store (rename_lit rn_id x y t1, rename_lit rn_expr x y e1, rename_lit rn_id x y t2, rename_lit rn_expr x y e2)
    | Cmpxchg (v, t1, e1, t2, e2, t3, e3) -> Cmpxchg (replace x y v, rename_lit rn_id x y t1, rename_lit rn_expr x y e1, rename_lit rn_id x y t2,
        rename_lit rn_expr x y e2, rename_lit rn_id x y t3, rename_lit rn_expr x y e3)
    | IsPointer e -> IsPointer (rename_lit rn_expr x y e)

let rn_pat : string -> string -> pattern<string> -> pattern<string> = rename_lit rn_instr

(* Z3 does pattern-matching and substitution, and free vars are calculated by reflection,
   so we're ready to test with no prep! *)
type LLVM_const = LLVM_expr<string, int>
type c_instr = LLVM_instr<string, LLVM_type, LLVM_const, LLVM_op, LLVM_cmp>

let llvm_cfg1 = { Nodes = set [1; 2; 3]; Edges = set [(1, 2, Seq); (2, 3, Seq)]; Start = 1;
                    Label = new Map<int, c_instr>(List.toSeq [(1, Br_label); 
                        (2, Br_label); (3, Br_label)]) }
let llvm_cfg1' = { Nodes = set [1; 2; 3]; Edges = set [(1, 2, Seq); (3, 2, Seq)]; Start = 1;
                    Label = new Map<int, c_instr>(List.toSeq [(1, Br_label); 
                        (2, Br_label); (3, Br_label)]) }
let llvm_cfg2 = { Nodes = set [4; 5; 6; 7]; 
Edges = set [(4, 5, Seq); (5, 6, Seq); (5, 7, Seq); (6, 7, Seq)]; 
Start = 4;
Label = new Map<int, c_instr>(List.toSeq [(4, Br_label); 
(5, Alloca ("x", Int_ty)); (6, Br_label); (7, Br_label)]) }

type pred = simple_pred<LLVM_edge_type, pattern<string>>
type trans = transform<string, LLVM_edge_type, pattern<string>, pred>
let llvm_trans : trans = TSeq (TSat ("n", SCPred (Stmt (Inj (Alloca ("c", MVar "d"))))), TA (ARelabelNode ("n", Inj Br_label)))

let test_trans T cfgs =
    let time = System.Diagnostics.Stopwatch.StartNew()
    let result = trans_sf mk_simple_pred2 freevars freevars freevars rn_id rn_pat (rn_pred rn_id rn_pat) (fun s p -> subst s p :?> LLVM_edge_type) (fun s p -> let a = subst s p in [|for v in (a :?> obj[]) -> v :?> (int * LLVM_edge_type)|]) (fun s p -> Some (subst s p :?> c_instr)) T empty_model cfgs
    time.Stop()
    printfn "%i" time.ElapsedMilliseconds
    let writer2 = System.IO.File.CreateText("results.txt")
    List.iter (fun (G, s) -> print_graph G; write_graph writer2 G; printfn "%A" s; ignore (System.Console.Read())) result
    fprintfn writer "%A" result
    writer.Flush()
    writer2.Flush()
    writer2.Close()
    result

(* sample transformations *)
let srn_cond = SCAnd (SCNot (SCPred AtStart),
  SCNot (SCExs [("_m", typeof<int>); ("_d", typeof<LLVM_edge_type>)] (SCPred (In ("_m", MVar "_d")))))

let safe_remove_node n : trans = TSeq (TSat (n, srn_cond), TA (ARemoveNode n))

let delete_inaccessible_nodes : trans = TSeq (TStar (TExists ("_n", (safe_remove_node "_n"))),
  TNot (TExists ("_n", TSat ("_n", srn_cond))))

let safe_move_edge n d m1 m2 : trans = TSeq (TExists ("_l", TExists ("_s", TSeq (
  TSat (m1, SCAnd (stmt (MVar "_l"), SCPred (Out_edges (MVar "_s")))),
  TSat (m2, SCAnd (stmt (MVar "_l"), SCPred (Out_edges (MVar "_s"))))))),
  TA (AMoveEdge (n, d, m1, m2)))

let copy_node n n' : trans = TExists ("_l", TExists ("_s", TSeq (
  TSat (n, SCAnds [stmt (MVar "_l"); SCPred (Out_edges (MVar "_s")); SCPred (Fresh n')]),
  TA (AAddNode (n', MVar "_l", MVar "_s")))))

let has_loop_through m n = SCAnd (node n, SCEX (SCEF (SCAnd (node m, SCEF (node n)))))

let entry_for_loop_through m n = SCAnds [node n; has_loop_through m n; SCEY (SCEx ("_kn", typeof<int>, (SCAnd (node "_kn", SCNot (has_loop_through m "_kn")))))]

(* I am at n, and there is a loop through n, and at every step on that loop
   that is not n there is at most one edge in.
   I am at n, and for every node not equal to n, if n is in the future of
   this node, then this node has at most one in edge.
   node n and (AF (not node n and (EF node n)) imp
    (for all m1 d1 m2 d2. (in(m1,d1) and in(m2,d2)) imp ((m1 = m2) and (d1 = d2))))
*)
let unique_in_edge_on_loop_through n : side_cond<string, pred> =
    SCAnd (node n,
        SCAG (SCImp (SCAnd (SCNot (node n),
                            SCEF (node n)),
                     SCAlls [("_m1", typeof<int>); ("_d1", typeof<LLVM_edge_type>);
                             ("_m2", typeof<int>); ("_d2", typeof<LLVM_edge_type>)]
                            (SCImp (SCAnd (SCPred (In ("_m1", (MVar "_d1"))),
                                           SCPred (In ("_m2", (MVar "_d2")))),
                                    SCAnd (SCPred (Is (Intv "_m1", Intv "_m2")),
                                           SCPred (PEq ("_d1", "_d2"))))))))


let slp_cond m d n = SCEY (SCAnds [node m; out n d; SCAH (SCNot (node n))])

let simple_loop_peel n = TSeqs [
  TSat (n, SCAnd (entry_for_loop_through n n, unique_in_edge_on_loop_through n));
  TExists ("_n'", TSeq (copy_node n "_n'", TSeq (
    TStar (TExists ("_m", TExists ("_d", TSeq (
      TSat (n, slp_cond "_m" (MVar "_d") n),
      safe_move_edge "_m" (MVar "_d") n "_n'")))),
    TSat (n, SCNot (SCExs [("_m", typeof<int>); ("_d", typeof<LLVM_edge_type>)] (slp_cond "_m" (MVar "_d") n))))));
  TStar (TExists ("_k", TSeq (TSat ("_k", SCAnd (SCNot (node n), entry_for_loop_through n "_k")),
    TExists ("_k'", TSeqs [copy_node "_k" "_k'"; TStar (
      TExists ("_m", TExists ("_d", TSeq (
        TSat ("_k", slp_cond "_m" (MVar "_d") "_k"),
        safe_move_edge "_m" (MVar "_d") "_k" "_k'"))));
      TSat ("_k", SCNot (SCExs [("_m", typeof<int>); ("_d", typeof<LLVM_edge_type>)] (slp_cond "_m" (MVar "_d") "_k")))]))));
  TSat (n, SCAG (SCImp (SCEx ("_k", typeof<int>, SCAnd (node "_k", entry_for_loop_through n "_k")), node n)))]

let loop_cfg1 = { Nodes = set [1; 2; 3]; Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 2, Seq)]; Start = 1;
                    Label = new Map<int, c_instr>(List.toSeq [(1, Br_label); 
                        (2, Br_label); (3, Br_label)]) }

let unfolded_cfg1 = { Nodes = set [1; 2; 3; 4; 5]; Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 2, Seq); (4, 5, Seq); (5, 2, Seq)]; Start = 1;
                    Label = new Map<int, c_instr>(List.toSeq [(1, Br_label); 
                        (2, Br_label); (3, Br_label); (4, Br_label); (5, Br_label)]) }

let fact_cfg = { Nodes = set [1; 2; 3; 4; 5; 6; 7; 8; 9];
                 Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 4, Seq); (4, 5, Seq); (5, 6, False); (5, 9, True); (6, 7, Seq); (7, 8, Seq); (8, 4, Seq)];
                 Start = 1;
                 Label = new Map<int, c_instr>(List.toSeq [(1, Assign ("x", Add, Int_ty, CInt 5, CInt 0));
                                                           (2, Assign ("i", Add, Int_ty, CInt 0, CInt 0));
                                                           (3, Assign ("r", Add, Int_ty, CInt 1, CInt 0));
                                                           (4, ICmp ("b", Slt, Int_ty, Local "i", Local "x"));
                                                           (5, Br_i1 (Local "b"));
                                                           (6, Assign ("i", Add, Int_ty, Local "i", CInt 1));
                                                           (7, Assign ("r", Mul, Int_ty, Local "i", Local "r"));
                                                           (8, Br_label); (9, Br_label)]) }

let branch_cfg = { Nodes = set [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12];
                 Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 4, False); (3, 12, True); (4, 5, Seq); (5, 6, Seq); (6, 7, False); (6, 2, True);
                              (7, 8, Seq); (8, 9, Seq); (9, 10, False); (9, 2, True); (10, 11, Seq); (11, 2, Seq)];
                 Start = 1;
                 Label = new Map<int, c_instr>(List.toSeq [(1, Assign ("x", Add, Int_ty, CInt 5, CInt 0));
                                                           (2, ICmp ("b", Sle, Int_ty, Local "x", CInt 0));
                                                           (3, Br_i1 (Local "b"));
                                                           (4, Assign ("y", Mul, Int_ty, Local "x", CInt 2));
                                                           (5, ICmp ("b1", Sle, Int_ty, Local "y", CInt 7));
                                                           (6, Br_i1 (Local "b1"));
                                                           (7, Assign ("y", Sub, Int_ty, Local "y", CInt 1));
                                                           (8, ICmp ("b2", Sle, Int_ty, Local "x", Local "y"));
                                                           (9, Br_i1 (Local "b2"));
                                                           (10, Assign ("x", Sub, Int_ty, Local "x", Local "y"));
                                                           (11, Br_label);
                                                           (12, Br_label)]) }

(*ignore (test_trans (simple_loop_peel "_n") fact_cfg)*)
(*ignore (test_trans (simple_loop_peel "_n") branch_cfg)*)

(* Code for skip deletion and insertion *)
let skip_deletion n =
  TSeq (TExists ("_m", TSeq (TSat (n, SCAnd (SCPred (Stmt (Inj Br_label)),
                                             SCPred (Out ("_m", Inj Seq)))),
     TSeq (TStar (TExists ("_n'", (TExists ("_d",
         (TSeq(TSat(n, SCPred (In ("_n'", MVar "_d"))),
               TA (AMoveEdge ("_n'",MVar "_d",n,"_m")))))))),
      TSat(n, SCNot (SCExs [("_n'", typeof<int>); ("_d", typeof<LLVM_edge_type>)]
                          (SCPred (In ("_n'", MVar "_d")))))))),
   safe_remove_node n)

let move_edge_to_skip m d n n' =
   TSeqs [TSat (n', SCAnd (SCPred (Stmt (Inj Br_label)),
                          SCPred (Out (n, Inj Seq))));
          TSat (m, SCPred (Out (n, MVar d)));
          TA (AMoveEdge (m, MVar d, n, n'))]

let skip_insert_in_edge m d n n' =
     TSeqs [TSat (n, SCPred (Fresh n'));
            TA (AAddNode (n', Inj Br_label, Inj[(n, Inj Seq)]));
            TSat (n, SCPred (In (m, MVar d))); 
            move_edge_to_skip m d n n']

let skip_insert_before_node n n' =
    TSeqs[TSat (n, SCPred (Fresh n'));
          TA (AAddNode (n', Inj Br_label, Inj[(n, Inj Seq)]));
          TStar (TExists ("_m1", TExists ("_d1", TSeq (
                 TSat (n, SCPred (In ("_m1", (MVar "_d1")))),
                 move_edge_to_skip "_m1" "_d1" n n'))));
          TSat (n, SCNot (SCExs [("_m1", typeof<int>);
                                 ("_d1", typeof<LLVM_edge_type>)] 
                                (SCPred (In ("_m1", MVar "_d1")))))]

let skip_insert_before_loop n n' =
    TSeqs[TSat (n, SCAnd(entry_for_loop_through n n,SCPred (Fresh n')));
          TA (AAddNode (n', Inj Br_label, Inj[(n, Inj Seq)]));
          TStar (TExists ("_m17", TExists ("_d17", TSeq (
                 TSat (n, SCAnds[SCPred (In ("_m17", (MVar "_d17")));
                                 SCNot(has_loop_through "_m17" n);
                                 SCNot (SCPred (Is (Intv "_m17", Intv n')))]),
                 move_edge_to_skip "_m17" "_d17" n n'))));
          TSat (n, SCNot (SCExs [("_m17", typeof<int>);
                                 ("_d17", typeof<LLVM_edge_type>)] 
                                (SCAnds[SCPred (In ("_m17", MVar "_d17"));
                                        SCNot(has_loop_through "_m17" n);
                                        SCNot (SCPred (Is (Intv "_m17", Intv n')))])))]

let def v = SCExs [("_opr", typeof<LLVM_op>); ("_ty1", typeof<LLVM_type>); ("_ty2", typeof<LLVM_type>); ("_ty3", typeof<LLVM_type>); 
                     ("_e1", typeof<LLVM_const>); ("_e2", typeof<LLVM_const>); ("_e3", typeof<LLVM_const>); ("_cmp", typeof<LLVM_cmp>)]
                    (SCOrs [stmt (Inj (Assign (v, MVar "_opr", MVar "_ty1", MVar "_e1", MVar "_e2")));
                            stmt (Inj (ICmp (v, MVar "_cmp", MVar "_ty1", MVar "_e1", MVar "_e2")));
                            stmt (Inj (Alloca (v, MVar "_ty1")));
                            stmt (Inj (Load (v, MVar "_ty1", MVar "_e1")));
                            stmt (Inj (Cmpxchg (v, MVar "_t1", MVar "_e1", MVar "_t2", MVar "_e2", MVar "_t3", MVar "_e3")))])

let used v = SCExs [("_xu", typeof<string>); ("_opr", typeof<LLVM_op>); ("_ty1", typeof<LLVM_type>); ("_ty2", typeof<LLVM_type>); ("_ty3", typeof<LLVM_type>); 
                     ("_e1", typeof<LLVM_const>); ("_e2", typeof<LLVM_const>); ("_e3", typeof<LLVM_const>); ("_cmp", typeof<LLVM_cmp>)]
                    (SCOrs [stmt (Inj (Assign ("_xu", MVar "_opr", MVar "_ty1", Inj (Local v), MVar "_e2")));
                            stmt (Inj (Assign ("_xu", MVar "_opr", MVar "_ty1", MVar "_e1", Inj (Local v))));
                            stmt (Inj (ICmp ("_xu", MVar "_cmp", MVar "_ty1", Inj (Local v), MVar "_e2")));
                            stmt (Inj (ICmp ("_xu", MVar "_cmp", MVar "_ty1", MVar "_e1", Inj (Local v))));
                            stmt (Inj (Br_i1 (Inj (Local v))));
                            stmt (Inj (Load ("_xu", MVar "_ty1", Inj (Local v))));
                            stmt (Inj (Store (MVar "_ty1", Inj (Local v), MVar "_ty2", MVar "_e2")));
                            stmt (Inj (Store (MVar "_ty1", MVar "_e1", MVar "_ty2", Inj (Local v))));
                            stmt (Inj (Cmpxchg ("_xu", MVar "_t1", Inj (Local v), MVar "_t2", MVar "_e2", MVar "_t3", MVar "_e3")));
                            stmt (Inj (Cmpxchg ("_xu", MVar "_t1", MVar "_e1", MVar "_t2", Inj (Local v), MVar "_t3", MVar "_e3")));
                            stmt (Inj (Cmpxchg ("_xu", MVar "_t1", MVar "_e1", MVar "_t2", MVar "_e2", MVar "_t3", Inj (Local v))))])

let alters_at_most x =
    SCExs [("_opr", typeof<LLVM_op>); ("_ty1", typeof<LLVM_type>);
           ("_e1", typeof<LLVM_const>); ("_e2", typeof<LLVM_const>);
           ("_cmp", typeof<LLVM_cmp>)]
          (SCOrs [stmt (Inj (Assign (x, MVar "_opr", MVar "_ty1",
                                    MVar "_e1", MVar "_e2")));
                  stmt (Inj (ICmp (x, MVar "_cmp", MVar "_ty1",
                                   MVar "_e1", MVar "_e2")));
                  stmt (Inj (Load (x, MVar "_ty1", MVar "_e1")))])

let uses x = used x

let is_dead_for x =
    SCAnds [alters_at_most x; SCNot (uses x);
            SCNot(SCEX (SCEU (SCNot (def x), uses x)))]

let dead_code_elimination n x =
    TSeq(TSat (n, is_dead_for x),
         TA (ARelabelNode (n, Inj Br_label)))

let dead_code_insertion n l =
    TSeqs[TSat(n, stmt (Inj Br_label));
          TA (ARelabelNode (n, l));
          TSat(n, SCEx("_x", typeof<string>, is_dead_for "_x"))]

let is_redundant_assign l =
    SCEx ("_x", typeof<string>,
          SCAnds[stmt (MVar l); alters_at_most "_x"; SCNot (uses "_x");
                 SCEx ("_y", typeof<string>, SCAnd(uses "_y", SCEB ((SCNot (stmt (MVar l))), (def "_y"))));
                 SCAY (SCAB (SCNot (def "_x"), stmt (MVar l)))])

let redundant_assignment_elimination n l =
    TSeq(TSat(n, is_redundant_assign l), TA (ARelabelNode (n, Inj Br_label)))

let redundant_assignment_insertion n l =
    TSeqs[TSat(n, stmt (Inj Br_label));
          TA (ARelabelNode (n, (MVar l)));
          TSat(n, is_redundant_assign l)]

let can_reduce_mult_to_add n x i c k =
    let cont_cond = SCAnds[SCNot (def x); SCNot(def i); SCNot start] in
    let asgn_x = stmt (Inj (Assign(x, Inj Mul, Inj Int_ty,
                                   Inj (Local i), Inj (CInt (MVar c)))))
    let asgn_i = stmt (Inj (Assign(i, Inj Add, Inj Int_ty,
                                   Inj (Local i), Inj (CInt (MVar k))))) in
    SCAnds [asgn_x; SCNot (SCPred (PEq (x, i))); SCEP asgn_i;
            SCNot (SCEY (SCEB (cont_cond,
                   (SCOr (SCAnd (SCNot cont_cond, SCNot asgn_i),
                         (SCAnd (asgn_i,
                                 (SCEY (SCEB (cont_cond,
                                              SCAnd (SCNot cont_cond,
                                                     SCNot asgn_x)))))))))))]
 
let reduce_mult_to_add n x i c k =
    TExists ("_c_result",
     (TSeq(TSat (n, SCAnd(can_reduce_mult_to_add n x i c k,
                          SCPred(Is(Intv "_c_result", Times(Intv c, Intv k))))),
           TA (ARelabelNode(n, Inj (Assign(x, Inj Add, Inj Int_ty,
                                           Inj (Local x),
                                           Inj (CInt (MVar "_c_result")))))))))

let loop_mult_to_add_candidate m n x i c =
    SCAnd (entry_for_loop_through n m,
           SCEF (SCAnds[node n;
                        stmt (Inj (Assign(x, Inj Mul, Inj Int_ty,
                              Inj (Local i), Inj (CInt (MVar c)))));
                        SCNot (SCPred (PEq (x, i)))]))

let loop_reduce_mult_to_add n : trans =
    TExist ["_m"; "_x"; "_i"; "_c"; "_k"]
           (TSeq(TSat("_m",loop_mult_to_add_candidate "_m" n "_x" "_i" "_c"),
                 TExists ("_n'",
                          TSeqs[skip_insert_before_loop "_m" "_n'";
                                dead_code_insertion "_n'"
                                    (Inj (Assign("_x", Inj Mul, Inj Int_ty,
                                                 Inj (Local "_i"),
                                                 Inj (CInt (MVar "_c")))));
                          reduce_mult_to_add n "_x" "_i" "_c" "_k"])))
(* Simple example:
%l1: %i = add int 0 0
%l2: %b = icmp lt %i 5
 %l3: br i1 %b %l7
 %l4: %i = add int %i 2
 %l5: %x = mul int %i 7
 %l6: br %l2
%l7: br %l7
*)

let simple_mult_to_add_example_cfg =
    {Nodes = set [1; 2; 3; 4; 5; 6; 7];
     Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 4, False);
                  (3, 7, True); (4, 5, Seq); (5, 6, Seq); (6, 2, Seq)];
     Start = 1;
     Label =
      new Map<int, c_instr>(List.toSeq 
       [(1, Assign ("i", Add, Int_ty, CInt 0, CInt 0));
        (2, ICmp ("b", Slt, Int_ty, Local "i", CInt 5));
        (3, Br_i1 (Local "b"));
        (4, Assign ("i", Add, Int_ty, Local "i", CInt 2));
        (5, Assign ("x", Mul, Int_ty, Local "i", CInt 7));
        (6, Br_label);
        (7, Br_label)]) }

(*ignore (test_trans (loop_reduce_mult_to_add "n") simple_mult_to_add_example_cfg)*)

(*

result = 0;
i = 0;
while (i <= 5) od
  i = i + 1;
  count = i * 3;
  j = 0;
  while (j <= 3) do
    result = result + count + j
    j = j + 1
  od
od

// Before being transformed:
%l1: %result = add int 0 0;
%l2: %i = add int 0 0;
%l3: %bi = icmp <= int %i 5;
  %l4: br i1 %bi %l15
  %l5: %i = add int %i 1 
  %l6: %count = mul int %i 3;
  %l7: %j = add int 0 0;
  %l8: %bj = icmp <= int %j 3;
    %l9: br i1 %bj %l14
    %l10: %result = add int %result %count
    %l11: %result = add int %result %j
    %l12: %j = add int %j 1
    %l13:% br %l8
  %l14: br %l3
%l15: br %l15


// After being transformed
%l1: %result = add int 0 0;
%l2: %i = add int 0 0;
%l16: %count = mul int %i 3;
%l3: %bi = icmp <= int %i 5;
  %l4: br i1 %bi %l15
  %l5: %i = add int %i 1 
  %l6: %count = add int %i 3;
  %l7: %j = add int 0 0;
  %l8: %bj = icmp <= int %j 3;
    %l9: br i1 %bj %l13
    %l10: %result = add int %result %count
    %l11: %result = add int %result %j
    %l12: %j = add int %j 1
    %l13:% br %l7
  %l14: br %l3
%l15: br %l15

*)

let mult_to_add_example_cfg =
    {Nodes = set [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15];
     Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 4, Seq); (4, 5, False);
                  (4, 15, True); (5, 6, Seq); (6, 7, Seq); (7, 8, Seq);
                  (8, 9, Seq); (9, 10, False); (9, 14, True); (10, 11, Seq);
                  (11, 12, Seq); (12, 13, Seq); (13, 8, Seq); (14, 3, Seq)];
     Start = 1;
     Label =
      new Map<int, c_instr>(List.toSeq 
       [(1, Assign ("result", Add, Int_ty, CInt 0, CInt 0));
        (2, Assign ("i", Add, Int_ty, CInt 0, CInt 0));
        (3, ICmp ("bi", Sle, Int_ty, Local "i", CInt 5));
        (4, Br_i1 (Local "bi"));
        (5, Assign ("i", Add, Int_ty, Local "i", CInt 1));
        (6, Assign ("count", Mul, Int_ty, Local "i", CInt 3));
        (7, Assign ("j", Add, Int_ty, CInt 0, CInt 0));
        (8, ICmp ("bj", Sle, Int_ty, Local "j", CInt 3));
        (9, Br_i1 (Local "bj"));
        (10, Assign ("result", Add, Int_ty, Local "result", Local "count"));
        (11, Assign ("result", Add, Int_ty, Local "result", Local "j"));
        (12, Assign ("j", Add, Int_ty, Local "j", CInt 1));
        (13, Br_label);
        (14, Br_label);
        (15, Br_label)]) }


(*ignore (test_trans (loop_reduce_mult_to_add "n") mult_to_add_example_cfg)*)

let not_loads e = SCNot (SCEx ("_x", typeof<string>, SCEx ("_ty", typeof<LLVM_type>, stmt (Inj (Load ("_x", MVar "_ty", e))))))
let not_stores e = SCNot (SCExs [("_e", typeof<LLVM_const>); ("_ty1", typeof<LLVM_type>); ("_ty2", typeof<LLVM_type>)] 
                                 (stmt (Inj (Store (MVar "_ty1", MVar "_e", MVar "_ty2", e)))))

let RSE1:trans = TExists ("n", TExists ("e2", TIf (ARelabelNode ("n", Inj (IsPointer (Inj (Local "e2")))), "n",
    SCAnds [stmt (Inj (Store (MVar "ty1", MVar "e1", MVar "ty2", Inj (Local "e2"))));
            SCAU (SCAnd (SCAll ("e", typeof<LLVM_const>, not_loads (MVar "e")), SCNot (def "l")), 
            SCAnd (SCNot (node "n"), stmt (Inj (Store (MVar "ty1'", MVar "e1'", MVar "ty2'", Inj (Local "e2"))))))])))

let RSE_fail1 = { Nodes = set [1; 2; 3; 4]; Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 4, Seq)]; Start = 1;
                    Label = new Map<int, c_instr>(List.toSeq [(1, Store (Int_ty, CInt 1, Pointer_ty Int_ty, Local "x")); 
                                                              (2, Load ("x", Int_ty, Local "x")); 
                                                              (3, Store (Int_ty, CInt 3, Pointer_ty Int_ty, Local "x"))]) }

let RSE_fail2 = { Nodes = set [1; 2; 3; 4]; Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 4, Seq)]; Start = 1;
                    Label = new Map<int, c_instr>(List.toSeq [(1, Store (Int_ty, CInt 1, Pointer_ty Int_ty, Local "x")); 
                                                              (2, Assign ("x", Add, Pointer_ty Int_ty, Local "x", CPointer 1)); 
                                                              (3, Store (Int_ty, CInt 3, Pointer_ty Int_ty, Local "x"))]) }

let RSE_fail3 = { Nodes = set [1; 2; 3; 4; 5]; Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 4, Seq); (4, 5, Seq)]; Start = 1;
                    Label = new Map<int, c_instr>(List.toSeq [(1, Store (Int_ty, CInt 1, Pointer_ty Int_ty, Local "x")); 
                                                              (2, Assign ("y", Add, Pointer_ty Int_ty, Local "x", CPointer 0)); 
                                                              (3, Load ("z", Pointer_ty Int_ty, Local "y"));
                                                              (4, Store (Int_ty, CInt 3, Pointer_ty Int_ty, Local "x"))]) }

let RSE_cfg2 = { Nodes = set [1; 2; 3; 4; 5; 6]; Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 4, Seq); (4, 5, Seq); (5, 6, Seq)]; Start = 1;
                    Label = new Map<int, c_instr>(List.toSeq [(1, Alloca ("x", Int_ty));
                                                              (2, Assign ("y", Add, Pointer_ty Int_ty, Local "x", CPointer 0));
                                                              (3, Store (Int_ty, CInt 1, Pointer_ty Int_ty, Local "x")); 
                                                              (4, Store (Int_ty, CInt 2, Pointer_ty Int_ty, Local "y")); 
                                                              (5, Store (Int_ty, CInt 3, Pointer_ty Int_ty, Local "x"))]) }

(*ignore (test_trans RSE1 RSE_cfg2)*)

(* Okay, sure, but: can we introduce new behavior? I bet we can. *)
let RSE_cfg3 = { Nodes = set [1; 2; 3; 4; 5; 6; 7; 8]; Start = 1;
                 Edges = set [(1, 2, Seq); (2, 3, Seq); (3, 4, Seq); (4, 5, Seq); (5, 6, Seq); (6, 7, Seq); (7, 8, Seq)];
                 Label = new Map<int, c_instr>(List.toSeq [(1, Alloca ("x", Int_ty));
                                                           (2, Assign ("y", Add, Pointer_ty Int_ty, Local "x", CPointer 0));
                                                           (3, Store (Pointer_ty Int_ty, Local "y", Pointer_ty (Pointer_ty Int_ty), CPointer 5)); 
                                                           (4, Store (Int_ty, CInt 0, Pointer_ty Int_ty, Local "x"));
                                                           (5, Store (Int_ty, CInt 1, Pointer_ty Int_ty, Local "x")); 
                                                           (6, Store (Int_ty, CInt 1, Pointer_ty Int_ty, CPointer 13)); 
                                                           (7, Store (Int_ty, CInt 3, Pointer_ty Int_ty, Local "x"))]) }

(*let RSE_result2 = test_trans (TStar RSE1) RSE_cfg3*)

(*printfn "%s" "\n(* Wonderful! Now for parallelism. *)\n"*)

let RSE_cfg4 = increment { Nodes = set [8; 9; 10; 11; 12; 13; 14; 15]; Start = 8;
                 Edges = set [(8, 9, Seq); (9, 10, Seq); (10, 11, Seq); (11, 12, Seq); (12, 13, True); (12, 14, False); (13, 15, Seq); (14, 15, Seq)]; 
                 Label = new Map<int, c_instr>(List.toSeq [(8, Load ("l", Pointer_ty (Pointer_ty Int_ty), CPointer 5)); (* use a global? *)
                                                           (9, Load ("w", Pointer_ty Int_ty, CPointer 13));
                                                           (10, Load ("v", Pointer_ty Int_ty, Local "l"));
                                                           (11, ICmp ("z", Sge, Int_ty, Local "v", Local "w"));
                                                           (12, Br_i1 (Local "z"));
                                                           (13, Store (Int_ty, CInt 7, Pointer_ty Int_ty, CPointer 9));
                                                           (14, Store (Int_ty, CInt 8, Pointer_ty Int_ty, CPointer 9))]) } 1

let merge map1 map2 = Map.fold (fun acc key value -> Map.add key value acc) map1 map2

let union G1 G2 = { Nodes = Set.union G1.Nodes G2.Nodes; Start = G1.Start;
  Edges = Set.union G1.Edges G2.Edges; Label = merge G1.Label G2.Label }

(*ignore (test_trans RSE1 (union RSE_cfg3 RSE_cfg4))*)

(*printfn "%s" "\n(* Now, how do we fix it? *)\n"*)

let RSE2:trans = TExists ("n", TExists ("e2", TIf (ARelabelNode ("n", Inj (IsPointer (Inj (Local "e2")))), "n",
    SCAnds [stmt (Inj (Store (MVar "ty1", MVar "e1", MVar "ty2", Inj (Local "e2"))));
            SCAU (SCAnd (SCOr (SCAll ("e", typeof<LLVM_const>, SCAnd (not_loads (MVar "e"), not_stores (MVar "e"))), node "n"), SCNot (def "e2")),
                  SCAnd (SCNot (node "n"), stmt (Inj (Store (MVar "ty1'", MVar "e1'", MVar "ty2'", Inj (Local "e2"))))))])))

(*let RSE_result4 = test_trans RSE2 (union RSE_cfg3 RSE_cfg4)*)

ignore (System.Console.Read())