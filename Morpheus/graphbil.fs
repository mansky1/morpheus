(* A CIL-like target language. *)
module GraphBIL

open Microsoft.Z3
open Morpheus

type BIL_type<'cname> = Tvoid | Int32 | Tclass of 'cname | Valueclass of 'cname | Tpointer of BIL_type<'cname>

type method_ref<'ty, 'cname, 'mname> = MRef of 'ty * 'cname * 'mname * 'ty list

type constr_ref<'ty, 'cname> = KRef of 'cname * 'ty list

type instr<'cname, 'ty, 'field, 'int_val, 'constr, 'mref> = 
    Ldc_i4 of 'int_val
  | Br
  | Brtrue
  | Brfalse
  | Ldind
  | Stind
  | Ldarga of 'int_val
  | Starg of 'int_val
  | Newobj of 'constr
  | Callvirt of 'mref
  | Callinstance of 'mref
  | Ret
  | Ldflda of 'ty * 'cname * 'field
  | Box of 'cname
  | Unbox of 'cname
  | Dup
  | Pop
  | Pop_pointer

type edge_type = Seq | Branch | Mcall of string

type pattern<'mvar> = literal<instr<'mvar, literal<BIL_type<'mvar>, 'mvar>, 'mvar, literal<int, 'mvar>, 
    literal<constr_ref<literal<BIL_type<'mvar>, 'mvar>, 'mvar>, 'mvar>, literal<method_ref<literal<BIL_type<'mvar>, 'mvar>, 'mvar, 'mvar>, 'mvar>>, 'mvar>

(* Z3 does pattern-matching and substitution, and free vars are calculated by reflection,
   so we're ready to test with no prep! *)
type c_instr = instr<string, BIL_type<string>, string, int, constr_ref<BIL_type<string>, string>, method_ref<BIL_type<string>, string, string>>

let BIL_cfg1 = { Nodes = set [1; 2; 3]; Edges = set [(1, 2, Seq); (2, 3, Seq)]; Starts = set [1];
                 Label = new Map<int, c_instr>(List.toSeq [(1, Br); (2, Br); (3, Br)]) }
let BIL_cfg2 = { Nodes = set [4; 5; 6; 7]; Edges = set [(4, 5, Seq); (5, 6, Seq); (5, 7, Branch); (6, 7, Seq)]; 
                 Starts = set [4]; Label = new Map<int, c_instr>(List.toSeq [(4, Br); (5, Ldflda (Int32, "Object", "num")); (6, Br); (7, Br)]) }

type trans = transform<string, edge_type, pattern<string>, simple_pred<edge_type, pattern<string>>>
let BIL_trans : trans = TSeq (TSat ("n", SCPred (Stmt (Inj (Ldflda (MVar "c", "d", "e"))))), TA (ARelabelNode ("n", Inj Br)))

let rn_id x y z = z

let rn_instr x y i = i

let rn_pat = rename_lit rn_instr

let test_trans T cfgs =
    let time = System.Diagnostics.Stopwatch.StartNew()
    let result = trans_sf mk_simple_pred2 freevars freevars freevars rn_id rn_pat (rn_pred rn_id rn_pat) (fun s p -> subst s p :?> edge_type) (fun s p -> Some (subst s p :?> c_instr)) T empty_model cfgs
    time.Stop()
    printfn "%i" time.ElapsedMilliseconds
    printfn "%A" result
    fprintfn writer "%A" result
    writer.Flush()
    result

ignore (test_trans BIL_trans BIL_cfg2)

ignore (System.Console.Read())