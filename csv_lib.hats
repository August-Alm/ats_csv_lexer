//#include "share/atspre_define.hats"
//#include "share/atspre_staload.hats"
//staload CSV = "csv_lexer_git.dats"
//staload UN = "prelude/SATS/unsafe.sats"

(* Definitions for more minimalist notation when working
 * with [stream_vt].
 *)
#define :: stream_vt_cons
#define nil stream_vt_nil
#define empty stream_vt_make_nil
(* For [list_vt]: *)
#define ** list_vt_append

(* ****** [Either] DATAVIEWTYPE ****** *)

datavtype
Either_bool
(a: vt0ype+, b: vt0ype+, bool) = 
Left(a, b, true) of a | Right(a, b, false) of b
                    
stadef
Either_bool = Either_bool

(* A linear version of the [Either] datatype, taking linear
 * types as arguments.
 *)
vtypedef  
Either
(a: vt0ype+, b: vt0ype+) = 
[p: bool] Either_bool(a, b, p)

fn {a, b: vt0ype} 
left(x: a):<> Either_bool(a, b, true) = Left(x)
        
fn {a, b: vt0ype}  
right(y: b):<> Either_bool(a, b, false) = Right(y) 
         
fn {a, b: vt0ype} 
is_left(z: !Either(a, b)): bool =
  case z of
  | Left(x) => true
  | _ => false
         
fn {a, b: vt0ype} 
is_right(z: !Either(a, b)): bool =
  case z of
  | Right(y) => true
  | _ => false

(* Templates for freeing linear variables. Mainly for local typechecking. *)
extern fun {a: vt0ype}
extfree(x: a): void

fun {a, b: vt0ype}
either_free(z: Either(a, b)): void =
  case z of
  | ~Left(x) => extfree<a>(x)
  | ~Right(y) => extfree<b>(y)

(* ****** FUNCTINONS ON [stream_vt] ****** *)

extern fun {a: vt0ype} 
stream_vt_filter$pred(x: !a): bool

extern fun {a, b: vt0ype}
stream_vt_usermap$fopr(x: a): b

fun {a, b: vt0ype}
stream_vt_usermap_aux (
    xs: stream_vt(a)
  ) : stream_vt(b) =
  $ldelay (
    case !xs of
    | ~nil() => nil()
    | ~(x :: xs1) => let
       val y = stream_vt_usermap$fopr(x)
     in  y :: stream_vt_usermap_aux(xs1) end
    ,
    ~xs
  )

fun {a, b: vt0ype}
stream_vt_usermap (
    xs: stream_vt(a),
    f: a -> b
  ) : stream_vt(b) = let
    implement stream_vt_usermap$fopr<a, b>(x) = f(x)
  in stream_vt_usermap_aux(xs) end

fun {a: vt0ype}
stream_vt_filter (
    xs: stream_vt(INV(a))
  ) : stream_vt(a) = 
  $ldelay ( 
    let val xs_con = !xs
    in case+ xs_con of
       | ~stream_vt_nil() => stream_vt_nil()
       | @stream_vt_cons(x, xs1) => 
         if stream_vt_filter$pred(x) then (
           xs1 := stream_vt_filter(xs1);
           fold@{a}(xs_con); 
           xs_con
         )
         else 
           let val xs1 = xs1 and x = x
           in free@{a}(xs_con);
              extfree<a>(x);
              !(stream_vt_filter(xs1))
           end 
    end 
    , 
    ~xs (* Second argument of [$ldelay]. *)
  ) 

fun {a, b: vt0ype}
filter_right (
    zs: stream_vt(Either(INV(a), INV(b)))
  ) : stream_vt(Either(a, b)) = 
  let
    implement 
    stream_vt_filter$pred<Either(a, b)>(z) = is_right(z)
  in
    stream_vt_filter<Either(a, b)>(zs)
  end

fun {a, b: vt0ype}
filter_left (
    zs: stream_vt(Either(INV(a), INV(b)))
  ) : stream_vt(Either(a, b)) = 
  let
    implement 
    stream_vt_filter$pred<Either(a, b)>(z) = is_left(z)
  in
    stream_vt_filter<Either(a, b)>(zs)
  end

fun {a, b: vt0ype}
map_right (
    zs: stream_vt(Either(INV(a), INV(b)))
  ) : stream_vt(b) =
  let
    val ws = filter_right(zs)
  
    fun {a, b: vt0ype}
    proj_right(z: Either(a, b)): b =
    case- z of
    | ~Right(y) => y
    
  in 
    stream_vt_usermap(ws, proj_right)
  end

fun {a, b: vt0ype}
map_left (
    zs: stream_vt(Either(INV(a), INV(b)))
  ) : stream_vt(a) =
  let
    val ws = filter_left(zs) 
  
    fun {a, b: vt0ype}
    proj_left(z: Either(a, b)): a =
    case- z of
    | ~Left(x) => x
    
  in 
    stream_vt_usermap(ws, proj_left)
  end

fun {a: t0ype}
span (
    xs: stream_vt(a),
    cond: !a -<cloref> bool
  ) : (List0_vt(a), stream_vt(a)) =
  case !xs of
  | ~nil() => (list_vt_nil(), empty()) 
  | ~stream_vt_cons(x, xs1) =>
    if cond(x) then
      let val (ys, zs) = span(xs1, cond)
      in (list_vt_cons(x, ys), zs)
      end
    else (list_vt_nil(), stream_vt_make_cons(x, xs1))

fun {a: t0ype}
stream_vt_group_by (
    xs: stream_vt(a),
    eq: a -> (a -<cloref> bool)
  ) : stream_vt(List0_vt(a)) =
  $ldelay (
    let val xs_con = !xs in
    case xs_con of
    | ~nil() => nil()
    | @stream_vt_cons(x, xs1) => let 
        val ex = x
        val (ys, zs) = span(xs1, eq(x))
        val cons = list_vt_cons(ex, ys)
      in
        free@{a}(xs_con); 
        cons :: stream_vt_group_by(zs, eq)
      end
    end
    ,
    ~xs
  )

(* ****** FUNCTIONS ON [list_vt] ****** *)

fun {res: vt0p}{a: t0p}
list_vt_foldleft_cloref (
    xs: List0_vt(INV(a)), 
    init: res, 
    fopr: (res, a) -<cloref1> res
  ) : res = 
  case xs of 
  | ~list_vt_nil() => init 
  | ~list_vt_cons(x0, xs1) => 
    let val init = fopr(init, x0)
        val xs1 = xs1 
    in list_vt_foldleft_cloref(xs1, init, fopr)
    end

(* Instead of a direct implementation of right fold we define it in
 * terms a reverse and a left fold. This is slower but it puts less
 * strain on the stack, which is important when dealing with CSV 
 * files that have a very large number of columns. 
 *)
fun {res: vt0p}{a: t0p}
list_vt_foldright_cloref (
    xs: List0_vt(INV(a)),
    init: res,
    fopr: (res, a) -<cloref1> res
  ) : res =
  list_vt_foldleft_cloref(list_vt_reverse(xs), init, fopr)

fun {a: t0p}
list_vt_partition (
    xs: List0_vt(INV(a)),
    pred: a -> bool
  ) : (List0_vt(a), List0_vt(a)) =
  let 
    vtypedef res = (List0_vt(a), List0_vt(a))
    val init = (list_vt_nil(), list_vt_nil())
    
    fn fopr ((ts, fs): res, x: a):<cloref1> res =
      if pred(x) then (list_vt_cons(x, ts), fs)
      else (ts, list_vt_cons(x, fs))
  in
    list_vt_foldright_cloref(xs, init, fopr)
  end 

extern fun {a, b: t0p}
list_vt_usermap$fopr(x: a): b

fun {a, b: t0p}
list_vt_usermap_aux(xs: List0_vt(a)): List0_vt(b) =
  case xs of
  | ~list_vt_nil() => list_vt_nil()
  | ~list_vt_cons(x, xs1) => let
      val y = list_vt_usermap$fopr(x)
    in list_vt_cons(y, list_vt_usermap_aux(xs1)) end

fun {a, b: t0p}
list_vt_usermap (
    xs: List0_vt(a),
    f: a -> b
  ) : List0_vt(b) = let
    implement list_vt_usermap$fopr<a, b>(x) = f(x)
  in list_vt_usermap_aux(xs) end
  
fun {a: t0p}
list_vt_head_opt(xs: !List0_vt(a)): Option_vt(a) = 
  case+ xs of
  | list_vt_nil() => None_vt()
  | list_vt_cons(x, xs1) => (Some_vt{a}(x))

fun {a: t0p}
list_vt2t(xs: List0_vt(a)): List0(a) = 
  case xs of
  | ~list_vt_nil() => list_nil()
  | ~list_vt_cons(x, xs1) => list_cons(x, list_vt2t(xs1))

fun {a: t0p}
list_vt_userfree(xs: List0_vt(a)): void =
  case xs of
  | ~list_vt_nil() => ()
  | ~list_vt_cons(x, xs1) => list_vt_userfree(xs1)


(* ****** IMPLEMENTATION OF [CSVState] ****** *)

(* Boilerplate to get nice dot-notation for the dataviewtype [CSVState] 
 * employed in the main file "csv_lexer.dats". 
 *)
local
  typedef CSVState_rec = @{
    tableRow = int, tableCol = int, textRow = int, textCol = int
  }
in
  datavtype (* Linear incarnation of [CSVState_rec]. *)
  CSVState = CSV_State of CSVState_rec

  fun {} state_init(i: int, j: int, k: int, l: int): CSVState =
  CSV_State @{ 
    tableRow = i, tableCol = j, textRow = k, textCol = l
  }

  fun {} state_free(st: CSVState): void =
  let val @CSV_State(s) = st in free@(st) end

  fun {} state_get_tableRow(st: !CSVState): int =
    let val CSV_State(s) = st in s.tableRow end
  fun {} state_get_tableCol(st: !CSVState): int =
    let val CSV_State(s) = st in s.tableCol end
  fun {} state_get_textRow(st: !CSVState): int =
    let val CSV_State(s) = st in s.textRow end
  fun {} state_get_textCol(st: !CSVState): int =
    let val CSV_State(s) = st in s.textCol end
  
  fun {} state_set_tableRow(st: !CSVState, i: int): void =
    let val @CSV_State(s) = st in s.tableRow := i; fold@(st) end
  fun {} state_set_tableCol(st: !CSVState, i: int): void =
    let val @CSV_State(s) = st in s.tableCol := i; fold@(st) end
  fun {} state_set_textRow(st: !CSVState, i: int): void =
    let val @CSV_State(s) = st in s.textRow := i; fold@(st) end
  fun {} state_set_textCol(st: !CSVState, i: int): void =
    let val @CSV_State(s) = st in s.textCol := i; fold@(st) end
  
  local
    infix +=
    macdef +=(x, i) = ,(x) := ,(x) + ,(i)
  in
    fun {} state_inc_tableRow(st: !CSVState, n: int): void =
      let val @CSV_State(s) = st in s.tableRow += n; fold@(st) end
    fun {} state_inc_tableCol(st: !CSVState, n: int): void =
      let val @CSV_State(s) = st in s.tableCol += n; fold@(st) end
    fun {} state_inc_textRow(st: !CSVState, n: int): void =
      let val @CSV_State(s) = st in s.textRow += n; fold@(st) end
    fun {} state_inc_textCol(st: !CSVState, n: int): void =
      let val @CSV_State(s) = st in s.textCol += n; fold@(st) end
  end
end

symintr .tableRow_inc .tableCol_inc .tableRow_inc .tableCol_inc
symintr .tableRow_set .tableCol_set .tableRow_set .tableCol_set
overload .tableRow with state_get_tableRow
overload .tableCol with state_get_tableCol
overload .textRow with state_get_textRow
overload .textCol with state_get_textCol
overload .tableRow_inc with state_inc_tableRow
overload .tableCol_inc with state_inc_tableCol
overload .textRow_inc with state_inc_textRow
overload .textCol_inc with state_inc_textCol
overload .tableRow_set with state_set_tableRow
overload .tableCol_set with state_set_tableCol
overload .textRow_set with state_set_textRow
overload .textCol_set with state_set_textCol

(* Boilerplate is finished. *)


//implement main0 () = ()
