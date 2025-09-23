open Ego.Basic
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

let cost_function score (sym, children) =
  let node_score =
    match Symbol.to_string sym with
    | "bv" -> 0.
    | "true" -> 0.
    | "false" -> 0.
    | "*" -> 1.
    | "/" -> 1.
    | "<<" -> 2.
    | _ -> 1.
  in
  node_score +. List.fold_left (fun acc vl -> acc +. score vl) 0. children

(* workaround: ZArith library doesn't like zero-length extracts *)
let checked_extract f v off len = if len > 0 then f v off len else Z.zero
let z_extract = checked_extract Z.extract
let z_signed_extract = checked_extract Z.signed_extract
let identity x = x

module PrimInt = struct
  type t = Z.t

  let pp = Z.pp_print
  let show i = Z.to_string i
  let equal i j = Z.equal i j
  let hash i = Z.hash i
end

module PrimQFBV = struct
  (* representation of bitvector positive Z.t and an explicit width*)

  type t = { w : int; v : Z.t }

  let true_value = { w = 1; v = Z.of_int 1 }
  let false_value = { w = 1; v = Z.of_int 0 }
  let booltobv = function true -> true_value | false -> false_value
  let show (b : t) = Printf.sprintf "0x%s:bv%d" (Z.format "%x" @@ b.v) b.w
  let pp fmt b = Format.pp_print_string fmt (show b)
  let ones ~(size : int) = z_extract Z.minus_one 0 size
  let zero ~(size : int) = { w = size; v = Z.zero }
  let empty = zero ~size:0
  let is_zero b = Z.equal Z.zero b.v
  let width (x : t) = match x with { w; v } -> w
  let value (b : t) : Z.t = match b with { w; v } -> v
  let to_signed_bigint b = z_signed_extract b.v 0 b.w
  let to_unsigned_bigint b = z_extract b.v 0 b.w
  let is_negative b = Z.lt (to_signed_bigint b) Z.zero
  let equal a b = Int.equal a.w b.w && Z.equal a.v b.v

  let compare a b =
    Int.compare a.w b.w |> function 0 -> Z.compare a.v b.v | o -> o

  let of_bigint ~(width : int) (v : Z.t) : t =
    assert (width >= 0);
    let v = z_extract v 0 width in
    { w = width; v }

  let of_int ~(width : int) i =
    assert (width > 0);
    let v = Z.of_int i in
    assert (Z.gt v (Z.of_int 0));
    of_bigint ~width v

  let of_string i =
    let vty = String.split_on_char ':' i in
    let w, v =
      match vty with
      | [ v; ty ] -> (
          String.to_seq ty |> List.of_seq |> function
          | 'b' :: 'v' :: width ->
              let width =
                Z.of_string
                  (String.concat "" (List.map (fun i -> String.make 1 i) width))
                |> Z.to_int
              in
              (width, Z.of_string v)
          | _ -> failwith "invalid format")
      | _ -> failwith "invalid format"
    in
    { w; v }

  let size_is_equal a b = assert (width a = width b)
  let bind f a = of_bigint ~width:a.w (f a.v)

  let bind2 f a b =
    size_is_equal a b;
    of_bigint ~width:a.w (f a.v b.v)

  let map2 f a b =
    size_is_equal a b;
    f a.v b.v

  let neg a = bind Z.neg a
  let add a b = bind2 Z.add a b
  let sub a b = bind2 Z.sub a b
  let bitnot a = bind Z.lognot a
  let bitand a b = bind2 Z.logand a b
  let bitor a b = bind2 Z.logor a b
  let bitxor a b = bind2 Z.logxor a b

  let udiv a b =
    size_is_equal a b;
    let v = if Z.equal b.v Z.zero then Z.minus_one else Z.div a.v b.v in
    of_bigint ~width:a.w v

  let sdiv a b =
    let neg_out = if is_negative a || is_negative b then neg else identity in
    let a = if is_negative a then neg a else a in
    let b = if is_negative b then neg b else b in
    neg_out (udiv a b)

  let urem a b = if is_zero b then a else bind2 Z.rem a b

  let srem a b =
    let neg_out = if is_negative a || is_negative b then neg else identity in
    let a = if is_negative a then neg a else a in
    let b = if is_negative b then neg b else b in
    neg_out (urem a b)

  let ult a b = map2 Z.lt a b
  let ugt a b = map2 Z.gt a b
  let ule a b = map2 Z.leq a b
  let uge a b = map2 Z.geq a b

  let map2_signed f a b =
    size_is_equal a b;
    f (to_signed_bigint a) (to_signed_bigint b)

  let slt a b = map2_signed Z.lt a b
  let sgt a b = map2_signed Z.gt a b
  let sle a b = map2_signed Z.leq a b
  let sge a b = map2_signed Z.geq a b
  let ashr a b = { w = a.w; v = Z.shift_right a.v (Z.to_int b.v) }
  let lshr a b = { w = a.w; v = Z.shift_right_trunc a.v (Z.to_int b.v) }
  let zero_extend ~(extension : int) b = { w = b.w + extension; v = b.v }

  let sign_extend ~(extension : int) b =
    let w = b.w + extension in
    let v = z_extract (z_signed_extract b.v 0 b.w) 0 w in
    { w; v }

  let concat a b =
    let a = zero_extend ~extension:b.w a in
    let a = { w = a.w; v = Z.shift_left a.v b.w } in
    let b = zero_extend ~extension:a.w b in
    bitor a b

  let repeat_bits ~(copies : int) a =
    List.init copies (fun _ -> a) |> List.fold_left concat empty
end

module BValue = struct
  type t = Integer of PrimInt.t | Bitvector of PrimQFBV.t | Boolean of bool
  [@@deriving show, eq]

  let show = function
    | Integer i -> PrimInt.show i
    | Bitvector i -> PrimQFBV.show i
    | Boolean i -> Bool.to_string i
end

let rec cleanup s =
  let open Sexplib0.Sexp in
  match s with
  | List (Atom "and" :: conjuncts) -> (
      let conjuncts = List.map cleanup conjuncts in
      match conjuncts with
      | h :: tl -> List.fold_left (fun a b -> List [ Atom "and"; a; b ]) h tl
      | _ -> failwith "nope")
  | List (Atom "or" :: disj) -> (
      let disj = List.map cleanup disj in
      match disj with
      | h :: tl -> List.fold_left (fun a b -> List [ Atom "or"; a; b ]) h tl
      | _ -> failwith "nope")
  | List os -> List (List.map cleanup os)
  | Atom _ as i -> i

module Gen = struct
  open Ego
  open Ego.Generic

  module L = struct
    type 'e shape =
      | True
      | False
      | BV of PrimQFBV.t
      | And of 'e list
      | Or of 'e list
      | Ite of 'e * 'e * 'e
      | Op of string * 'e list
    [@@deriving map, iter, fold, show, ord]

    type t = Mk of t shape [@@unboxed] [@@deriving show]

    let rec flatten_assoc (a : t) : t =
      (match a with
      | Mk (And [ Mk (And xs); Mk (And ys) ]) ->
          Mk (And (List.map flatten_assoc @@ xs @ ys))
      | Mk (And [ i; Mk (And xs) ]) ->
          Mk (And (List.map flatten_assoc @@ xs @ [ i ]))
      | Mk (Or [ i; Mk (Or xs) ]) ->
          Mk (Or (List.map flatten_assoc @@ xs @ [ i ]))
      | Mk (And [ Mk (And xs); i ]) ->
          Mk (And (List.map flatten_assoc @@ (i :: xs)))
      | Mk (Or [ Mk (Or xs); i ]) ->
          Mk (Or (List.map flatten_assoc @@ (i :: xs)))
      | Mk (Or xs) -> Mk (Or (List.map flatten_assoc xs))
      | Mk (And xs) -> Mk (And (List.map flatten_assoc xs))
      | Mk (Op (o, xs)) -> Mk (Op (o, List.map flatten_assoc xs))
      | Mk (Ite (a, b, c)) ->
          Mk (Ite (flatten_assoc a, flatten_assoc b, flatten_assoc c))
      | i -> i)
      |> function
      | Mk (And (h :: tl)) ->
          (List.fold_left (fun x y ->
               match (x, y) with
               | Mk (And xs), Mk (And ys) -> Mk (And (xs @ ys))
               | Mk (And xs), z -> Mk (And (xs @ [ z ]))
               | _ -> failwith "no"))
            (Mk (And [ h ])) tl
      | o -> o

    let rec to_sexp (consts : StringSet.t ref) e =
      let open Sexplib0.Sexp in
      match flatten_assoc e with
      | Mk True -> Atom "true"
      | Mk False -> Atom "true"
      | Mk (BV v) ->
          List
            [
              Atom "_"; Atom ("bv" ^ Z.to_string v.v); Atom (Int.to_string v.w);
            ]
      | Mk (And a) -> List (Atom "and" :: List.map (to_sexp consts) a)
      | Mk (Or a) -> List (Atom "or" :: List.map (to_sexp consts) a)
      | Mk (Ite (c, a, b)) ->
          List [ Atom "ite"; to_sexp consts a; to_sexp consts b ]
      | Mk (Op (c, [ x ])) when String.starts_with ~prefix:"extract" c -> (
          match String.split_on_char '_' c with
          | [ n; hi; lo ] ->
              List
                [
                  List [ Atom "_"; Atom "extract"; Atom hi; Atom lo ];
                  to_sexp consts x;
                ]
          | _ -> failwith "no")
      | Mk (Op (c, [])) ->
          consts := StringSet.add c !consts;
          Atom c
      | Mk (Op (c, args)) -> List (Atom c :: List.map (to_sexp consts) args)

    let rec of_sexp s : t =
      let open Sexplib0.Sexp in
      let s = cleanup s in
      match s with
      | List (Atom "and" :: conjuncts) ->
          let conjuncts = List.map of_sexp conjuncts in
          Mk (And conjuncts)
      | List (Atom "or" :: disj) ->
          let disj = List.map of_sexp disj in
          Mk (Or disj)
      | List [ List [ Atom "_"; Atom "extract"; Atom i; Atom j ]; arg ] ->
          let op = "extract_" ^ i ^ "_" ^ j in
          Mk (Op (op, [ of_sexp arg ]))
      | List [ Atom "_"; Atom bv; Atom i ]
        when String.starts_with ~prefix:"bv" bv ->
          let value = String.sub bv 2 (String.length bv - 2) in
          let v = PrimQFBV.of_string (value ^ ":bv" ^ i) in
          Mk (BV v)
      | List (Atom s :: os) -> Mk (Op (s, List.map of_sexp os))
      | Atom s -> Mk (Op (s, []))
      | o -> failwith @@ "unexpected sexpr: " ^ Sexplib0.Sexp.to_string o

    type op =
      | TrueOp
      | FalseOp
      | BVOp of PrimQFBV.t
      | AndOp
      | OrOp
      | IteOp
      | OpOp of string
    [@@deriving eq]

    let op_of_string s =
      let to_bv_opt =
        String.split_on_char ':' s |> function
        | [ i; j ] when String.starts_with ~prefix:"bv" j ->
            Some (PrimQFBV.of_string s)
        | _ -> None
      in
      match s with
      | o when String.starts_with ~prefix:"?" o ->
          failwith ("got wildcard : " ^ s)
      | "true" -> TrueOp
      | "false" -> FalseOp
      | "and" -> AndOp
      | "or" -> OrOp
      | "ite" -> IteOp
      | o when Option.is_some to_bv_opt -> BVOp (Option.get to_bv_opt)
      | s -> OpOp s

    let op = function
      | True -> TrueOp
      | False -> FalseOp
      | BV v -> BVOp v
      | And _ -> AndOp
      | Or _ -> OrOp
      | Ite _ -> IteOp
      | Op (n, _) -> OpOp n

    let make op childs =
      match (op, childs) with
      | TrueOp, _ -> True
      | FalseOp, _ -> False
      | AndOp, cs -> And cs
      | OrOp, cs -> Or cs
      | IteOp, [ c; a; b ] -> Ite (c, a, b)
      | BVOp v, _ -> BV v
      | OpOp s, cs -> Op (s, cs)
      | _ -> failwith "bad op constructor"

    let children s = List.rev @@ fold_shape (fun a b -> b :: a) [] s
    let map_children s f = map_shape f s
  end

  module A = struct
    type t = unit
    type value = BV of PrimQFBV.t | True | False [@@deriving eq, show]
    type data = value option [@@deriving show, eq]

    let default : data = None
    let equal_data a b = Option.equal equal_value a b
  end

  module MA
      (S :
        Ego.Generic.GRAPH_API
          with type 'p t = (Id.t L.shape, A.t, A.data, 'p) egraph
           and type analysis := A.t
           and type data := A.data
           and type 'a shape := 'a L.shape
           and type node := L.t) =
  struct
    type 'p t = (Ego.Id.t L.shape, A.t, A.data, 'p) Ego.Generic.egraph

    let bind2_bv op a =
      match a with
      | [ Some (A.BV l); Some (BV r) ] -> Some (A.BV (op l r))
      | _ -> None

    let bind2_bv_bool op a =
      match a with
      | [ Some (A.BV l); Some (BV r) ] -> (
          match op l r with true -> Some A.True | false -> Some False)
      | _ -> None

    let bind2_bv op a =
      match a with
      | [ Some (A.BV l); Some (BV r) ] -> Some (A.BV (op l r))
      | _ -> None

    let map_bv f a = match a with Some (A.BV a) -> Some (f a) | _ -> None

    let eval (v : A.data L.shape) : A.data =
      let open L in
      match v with
      | BV v -> Some (BV v)
      | True -> Some True
      | False -> Some False
      | Or ls
        when List.exists
               (function
                 | Some i when A.equal_value i True -> true | _ -> false)
               ls ->
          Some True
      | And ls
        when List.exists
               (function
                 | Some i when A.equal_value i True -> true | _ -> false)
               ls ->
          Some False
      | And ls
        when List.for_all
               (function
                 | Some i when A.equal_value i True -> true | _ -> false)
               ls ->
          Some True
      | Or ls
        when List.for_all
               (function
                 | Some i when A.equal_value i False -> true | _ -> false)
               ls ->
          Some False
      | Op ("not", [ Some True ]) -> Some False
      | Op ("not", [ Some False ]) -> Some True
      | Op ("bvadd", args) -> bind2_bv PrimQFBV.add args
      | Op ("bvand", args) -> bind2_bv PrimQFBV.bitand args
      | Op ("bvor", args) -> bind2_bv PrimQFBV.bitor args
      | Op ("bvxor", args) -> bind2_bv PrimQFBV.bitxor args
      | Op ("bvsub", args) -> bind2_bv PrimQFBV.sub args
      | Op ("bvnot", [ Some (BV r) ]) -> Some (BV (PrimQFBV.bitnot r))
      | Op ("bvneg", [ Some (BV r) ]) -> Some (BV (PrimQFBV.neg r))
      | Op ("bvsle", args) -> bind2_bv_bool PrimQFBV.sle args
      | Op ("bvslt", args) -> bind2_bv_bool PrimQFBV.slt args
      | Op ("bvsge", args) -> bind2_bv_bool PrimQFBV.sge args
      | Op ("bvsgt", args) -> bind2_bv_bool PrimQFBV.sgt args
      | Op ("bvule", args) -> bind2_bv_bool PrimQFBV.ule args
      | Op ("bvult", args) -> bind2_bv_bool PrimQFBV.ult args
      | Op ("bvuge", args) -> bind2_bv_bool PrimQFBV.uge args
      | Op ("bvugt", args) -> bind2_bv_bool PrimQFBV.ugt args
      | Op ("=", [ Some l; Some r ]) -> (
          match A.equal_value l r with true -> Some True | false -> Some False)
      | _ -> None

    let make : Ego.Generic.ro t -> Ego.Id.t L.shape -> A.data =
     fun graph term ->
      match term with
      | L.Op ("=", [ l; r ]) when S.class_equal graph l r -> Some True
      | term -> eval (L.map_children term (S.get_data graph))

    let merge : A.t -> A.data -> A.data -> A.data * (bool * bool) =
     fun s d d ->
      match (d, d) with
      | Some l, None -> (Some l, (false, true))
      | None, Some l -> (Some l, (true, false))
      | Some l, Some r when A.equal_value l r -> (Some l, (false, false))
      | Some l, Some r -> (None, (false, false))
      | None, None -> (None, (false, false))

    let modify : rw t -> Ego.Id.t -> unit =
     fun graph cls ->
      match S.get_data (S.freeze graph) cls with
      | None -> ()
      | Some (BV n) ->
          let nw_cls = S.add_node graph (L.Mk (BV n)) in
          S.merge graph nw_cls cls
      | Some True ->
          let nw_cls = S.add_node graph (L.Mk L.True) in
          S.merge graph nw_cls cls
      | Some False ->
          let nw_cls = S.add_node graph (L.Mk L.False) in
          S.merge graph nw_cls cls
  end

  module EGraph = Make (L) (A) (MA)

  module Cost = struct
    type t = float [@@deriving ord]

    let cost f shape =
      let open L in
      let c =
        List.fold_left (fun a b -> a +. b) 0. (List.map f (children shape))
      in
      match shape with
      | True -> 1.0
      | False -> 1.0
      | BV v -> 2.0
      | Op ("and", _) -> 20.0 +. c
      | Op ("or", _) -> 20.0 +. c
      | Op ("=>", _) -> 20.0 +. c
      | o -> 60.0 +. c
  end

  module Extractor = MakeExtractor (L) (Cost)

  type q = L.op Generic.Query.t

  let add_sexp graph e = EGraph.add_node graph (L.of_sexp e)
  let query s = Generic.Query.of_sexp L.op_of_string s

  let rewrite_rules =
    let open Sexplib0.Sexp in
    let open EGraph in
    let and_const_true =
      let from = query @@ List [ Atom "and"; Atom "?a"; Atom "?b" ] in
      let into = query @@ Atom "true" in
      let cond =
       fun graph enode emap ->
        EGraph.get_data (EGraph.freeze graph) enode |> function
        | Some a when a = A.True -> true
        | _ -> false
      in
      Rule.make_conditional ~from ~into ~cond
    in
    let and_const_false =
      let from = query @@ List [ Atom "and"; Atom "?a"; Atom "?b" ] in
      let into = query @@ Atom "false" in
      let cond =
       fun graph enode emap ->
        EGraph.get_data (EGraph.freeze graph) enode |> function
        | Some a when a = A.False -> true
        | _ -> false
      in
      Rule.make_conditional ~from ~into ~cond
    in
    let or_const_true =
      let from = query @@ List [ Atom "or"; Atom "?a"; Atom "?b" ] in
      let into = query @@ Atom "true" in
      let cond =
       fun graph enode emap ->
        EGraph.get_data (EGraph.freeze graph) enode |> function
        | Some a when a = A.True -> true
        | _ -> false
      in
      Rule.make_conditional ~from ~into ~cond
    in
    let or_const_false =
      let from = query @@ List [ Atom "or"; Atom "?a"; Atom "?b" ] in
      let into = query @@ Atom "false" in
      let cond =
       fun graph enode emap ->
        EGraph.get_data (EGraph.freeze graph) enode |> function
        | Some a when a = A.False -> true
        | _ -> false
      in
      Rule.make_conditional ~from ~into ~cond
    in

    let eq_rule =
      let from = query @@ List [ Atom "="; Atom "?a"; Atom "?b" ] in
      let into = query @@ Atom "true" in
      let cond =
       fun graph enode emap ->
        EGraph.class_equal (EGraph.freeze graph) (StringMap.find "a" emap)
          (StringMap.find "b" emap)
      in
      Rule.make_conditional ~from ~into ~cond
    in
    let eq_const_false =
      let from = query @@ List [ Atom "="; Atom "?a"; Atom "?b" ] in
      let into = query @@ Atom "false" in
      let cond =
       fun graph enode emap ->
        EGraph.get_data (EGraph.freeze graph) enode |> function
        | Some a when a = A.False -> true
        | _ -> false
      in
      Rule.make_conditional ~from ~into ~cond
    in
    let eq_rule_consts =
      let from = query @@ List [ Atom "="; Atom "?a"; Atom "?b" ] in
      let into = query @@ Atom "true" in
      let cond =
       fun graph enode emap ->
        let fg = EGraph.freeze graph in
        let a = EGraph.get_data fg (StringMap.find "a" emap) in
        let b = EGraph.get_data fg (StringMap.find "b" emap) in
        match (a, b) with Some a, Some b when a = b -> true | _ -> false
      in
      Rule.make_conditional ~from ~into ~cond
    in
    let ite_true =
      let from =
        query @@ List [ Atom "ite"; Atom "true"; Atom "?a"; Atom "?b" ]
      in
      let into = query @@ Atom "?a" in
      Rule.make_constant ~from ~into
    in
    let ite_false =
      let from =
        query @@ List [ Atom "ite"; Atom "false"; Atom "?a"; Atom "?b" ]
      in
      let into = query @@ Atom "?b" in
      Rule.make_constant ~from ~into
    in
    let and_simp_r =
      let from = query @@ List [ Atom "and"; Atom "?a"; Atom "true" ] in
      let into = query @@ Atom "?a" in
      Rule.make_constant ~from ~into
    in
    let and_simp_l =
      let from = query @@ List [ Atom "and"; Atom "true"; Atom "?a" ] in
      let into = query @@ Atom "?a" in
      Rule.make_constant ~from ~into
    in
    let and_true =
      let from = query @@ List [ Atom "and"; Atom "true"; Atom "true" ] in
      let into = query @@ Atom "true" in
      Rule.make_constant ~from ~into
    in
    let and_refute_l =
      let from = query @@ List [ Atom "and"; Atom "false"; Atom "?a" ] in
      let into = query @@ Atom "false" in
      Rule.make_constant ~from ~into
    in
    let and_refute_r =
      let from = query @@ List [ Atom "and"; Atom "?a"; Atom "false" ] in
      let into = query @@ Atom "false" in
      Rule.make_constant ~from ~into
    in
    let or_false_l =
      let from = query @@ List [ Atom "or"; Atom "false"; Atom "?a" ] in
      let into = query @@ Atom "?a" in
      Rule.make_constant ~from ~into
    in
    let or_false_r =
      let from = query @@ List [ Atom "or"; Atom "?a"; Atom "false" ] in
      let into = query @@ Atom "?a" in
      Rule.make_constant ~from ~into
    in
    let or_true_l =
      let from = query @@ List [ Atom "or"; Atom "true"; Atom "?a" ] in
      let into = query @@ Atom "true" in
      Rule.make_constant ~from ~into
    in
    let or_true_r =
      let from = query @@ List [ Atom "or"; Atom "?a"; Atom "true" ] in
      let into = query @@ Atom "true" in
      Rule.make_constant ~from ~into
    in
    let norm_impl =
      let from = query @@ List [ Atom "=>"; Atom "?l"; Atom "?r" ] in
      let into =
        query @@ List [ Atom "or"; Atom "?r"; List [ Atom "not"; Atom "?l" ] ]
      in
      Rule.make_constant ~from ~into
    in
    let double_negation =
      let from = query @@ List [ Atom "not"; List [ Atom "not"; Atom "?a" ] ] in
      let into = query @@ Atom "?a" in
      Rule.make_constant ~from ~into
    in
    let bool_inv =
      let from = query @@ List [ Atom "not"; Atom "true" ] in
      let into = query @@ Atom "false" in
      Rule.make_constant ~from ~into
    in
    [
      norm_impl;
      double_negation;
      ite_true;
      ite_false;
      and_simp_l;
      and_simp_r;
      eq_rule;
      bool_inv;
      (*
      eq_const_false;
      and_const_false;
      and_const_true;
      or_const_false;
      or_const_true;
      bool_inv;
      and_true;
      and_refute_l;
      and_refute_r;
      or_false_l;
      or_false_r;
      or_true_l;
      or_true_r;
      *)
    ]
end

let process fname =
  let open Sexplib0 in
  let open Gen in
  let graph = EGraph.init () in
  let x = Sexplib.Sexp.load_sexps fname in

  let add_if_equality grpah name e =
    let open Sexp in
    let ok n =
      String.starts_with ~prefix:"inv" n
      || String.starts_with ~prefix:"unnamed" n
    in
    match e with
    | List (Atom "=" :: rest) as o when ok name ->
        print_endline @@ "ground equality: " ^ Sexp.to_string o;
        let is = List.map (add_sexp graph) rest in
        let outer = add_sexp graph e in
        print_endline (Int.to_string @@ List.length is);
        (match is with
        | h :: tl -> List.iter (EGraph.merge graph h) tl
        | _ -> ());
        EGraph.rebuild graph;
        [ (name, e, outer) ]
    | o ->
        print_endline @@ "assert " ^ Sexp.to_string o;
        [ (name, o, add_sexp graph o) ]
  in

  let c = ref 0 in
  let fresh () =
    c := !c + 1;
    "unnamed_assert_" ^ Int.to_string !c
  in

  let consts = ref StringMap.empty in

  let add s =
    let open Sexp in
    match s with
    | List [ Atom "declare-const"; Atom const; ty ] ->
        consts := StringMap.add const ty !consts;
        []
    | List (Atom "set-logic" :: _) -> []
    | List (Atom "define-fun" :: _) -> []
    | List (Atom "check-sat" :: _) -> []
    | List [ Atom "assert"; List [ Atom "!"; s; Atom ":named"; Atom name ] ] ->
        print_endline @@ "add named assert (" ^ name ^ ") ";
        add_if_equality graph name s
    | List [ Atom "assert"; s ] as o ->
        print_endline @@ "add assert:\n" ^ Sexp.to_string o;
        add_if_equality graph (fresh ()) s
    | o -> failwith @@ "unexpected: " ^ Sexp.to_string o
  in
  let asserts = List.concat_map add x in
  let tr = add_sexp graph (Atom "true") in
  let fr = add_sexp graph (Atom "false") in

  EGraph.rebuild graph;

  let conj_asserts =
    List.map (function n, sexp, node -> sexp) asserts |> fun i ->
    Sexp.List (Sexp.Atom "and" :: i) |> cleanup |> add_sexp graph
  in
  let _ =
    EGraph.run_until_saturation ~fuel:`Unbounded ~node_limit:`Unbounded graph
      rewrite_rules
  in
  if EGraph.class_equal (EGraph.freeze graph) tr fr then print_endline "unsat";
  let used_consts = ref StringSet.empty in
  let print_exp n e =
    if not (EGraph.class_equal (EGraph.freeze graph) e tr) then (
      let e = L.to_sexp used_consts @@ Extractor.extract graph e in
      let oc = open_out ("simped_" ^ fname) in
      let f = Format.formatter_of_out_channel oc in
      Format.pp_print_string f "\n(set-logic QF_BV)\n";
      StringSet.to_list !used_consts
      |> List.concat_map (function s ->
             ( StringMap.find_opt s !consts |> function
               | Some i -> [ (s, i) ]
               | _ -> [] ))
      |> List.iter (function c, t ->
             Format.pp_print_string f @@ Sexp.to_string
             @@ List [ Atom "declare-const"; Atom c; t ];
             Format.pp_print_string f "\n");
      Sexp.pp_hum_indent 1 f
      @@ List [ Atom "assert"; List [ Atom "!"; e; Atom ":named"; Atom n ] ];
      Format.pp_print_string f "\n(check-sat)\n";
      close_out oc)
  in
  (*let e = StringMap.find "InvPrimed" exprs in
  print_exp "InvPrimed" e; *)
  (*List.iter (function n, e -> print_exp n e) asserts;*)
  print_exp "ConjAsserts" conj_asserts;
  ()

let () =
  let verbose = ref false in
  let input_files = ref "" in
  let anon_fun i = () in
  let speclist =
    [ ("-i", Arg.Set_string input_files, "Input file information") ]
  in
  Arg.parse speclist anon_fun "usage";
  process !input_files

(*

let () =
  let open Sexplib0 in
  let x = Sexplib.Sexp.load_sexps "test.smt2" in
  let graph = EGraph.init () in
  (* add expressions *)


  let c = ref 0 in
  let fresh () =
    c := !c + 1;
    "unnamed_assert_" ^ Int.to_string !c
  in

  let add_if_equality name e =
    let open Sexp in
    match e with
    | List (Atom "=" :: rest) as o ->
        print_endline @@ "ground equality: " ^ Sexp.to_string o;
        let is = List.map (EGraph.add_sexp graph) rest in
        let outer = EGraph.add_sexp graph e in
        print_endline (Int.to_string @@ List.length is);
        (match is with
        | h :: tl -> List.iter (EGraph.merge graph h) tl
        | _ -> ());
        EGraph.rebuild graph;
        [ (name, outer) ]
    | o ->
        print_endline @@ "assert " ^ Sexp.to_string o;
        [ (name, EGraph.add_sexp graph o) ]
  in

  let rules =
    let ite_true =
      let from =
        Query.of_sexp @@ List [ Atom "ite"; Atom "true"; Atom "?a"; Atom "?b" ]
      in
      let into = Query.of_sexp @@ List [ Atom "?a" ] in
      Rule.make ~from ~into |> Option.get
    in
    let ite_false =
      let from =
        Query.of_sexp @@ List [ Atom "ite"; Atom "false"; Atom "?a"; Atom "?b" ]
      in
      let into = Query.of_sexp @@ List [ Atom "?b" ] in
      Rule.make ~from ~into |> Option.get
    in
    let and_true =
      let from =
        Query.of_sexp @@ List [ Atom "and"; List [ Atom "true"; Atom "true" ] ]
      in
      let into = Query.of_sexp @@ List [ Atom "true" ] in
      Rule.make ~from ~into |> Option.get
    in
    let and_refute_l =
      let from =
        Query.of_sexp @@ List [ Atom "and"; List [ Atom "false"; Atom "?a" ] ]
      in
      let into = Query.of_sexp @@ List [ Atom "false" ] in
      Rule.make ~from ~into |> Option.get
    in
    let and_refute_r =
      let from =
        Query.of_sexp @@ List [ Atom "and"; List [ Atom "?a"; Atom "false" ] ]
      in
      let into = Query.of_sexp @@ List [ Atom "false" ] in
      Rule.make ~from ~into |> Option.get
    in
    let or_true_l =
      let from =
        Query.of_sexp @@ List [ Atom "or"; List [ Atom "true"; Atom "?a" ] ]
      in
      let into = Query.of_sexp @@ List [ Atom "true" ] in
      Rule.make ~from ~into |> Option.get
    in
    let or_refute =
      let from =
        Query.of_sexp
        @@ List [ Atom "and"; List [ Atom "false"; Atom "false" ] ]
      in
      let into = Query.of_sexp @@ List [ Atom "false" ] in
      Rule.make ~from ~into |> Option.get
    in
    let or_true_r =
      let from =
        Query.of_sexp @@ List [ Atom "and"; List [ Atom "?a"; Atom "true" ] ]
      in
      let into = Query.of_sexp @@ List [ Atom "true" ] in
      Rule.make ~from ~into |> Option.get
    in
    let impl =
      let from =
        Query.of_sexp @@ List [ Atom "=>"; List [ Atom "true"; Atom "?a" ] ]
      in
      let into = Query.of_sexp @@ List [ Atom "?a" ] in
      Rule.make ~from ~into |> Option.get
    in
    let impl_trivial =
      let from =
        Query.of_sexp @@ List [ Atom "=>"; List [ Atom "?a"; Atom "false" ] ]
      in
      let into = Query.of_sexp @@ List [ Atom "true" ] in
      Rule.make ~from ~into |> Option.get
    in
    [
      impl;
      impl_trivial;
      ite_true;
      ite_false;
      and_true;
      and_refute_l;
      and_refute_r;
      or_refute;
      or_true_l;
      or_true_r;
    ]
  in

  let add s =
    let open Sexp in
    match cleanup s with
    | List (Atom "declare-const" :: _) -> []
    | List (Atom "set-logic" :: _) -> []
    | List (Atom "define-fun" :: _) -> []
    | List (Atom "check-sat" :: _) -> []
    | List [ Atom "assert"; List [ Atom "!"; s; Atom ":named"; Atom name ] ] ->
        print_endline @@ "add named assert (" ^ name ^ ") ";
        add_if_equality name s
    | List [ Atom "assert"; s ] as o ->
        print_endline @@ "add assert:\n" ^ Sexp.to_string o;
        add_if_equality (fresh ()) s
    | o -> failwith @@ "unexpected: " ^ Sexp.to_string o
  in
  let exprs = List.concat_map add x in

  let asserts = StringMap.of_list exprs in
  let _ = EGraph.run_until_saturation graph rules in
  let e = StringMap.find "InvPrimed" asserts in
  let extr = EGraph.extract cost_function graph e in
  print_endline (Sexplib0.Sexp.to_string extr)
  *)
