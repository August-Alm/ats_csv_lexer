(* This program parses CSV data conforming to the RFC 4180 standard.      *) 
(* The algorithm uses the same over-arching logic as the Haskell package  *)
(* "lazy-csv" but makes significant use of features unique to ATS. In     *)
(* particular, it extensively uses linear types to almost entirely        *) 
(* eliminate the need for garbage collection. It does put strain on the   *)
(* stack space though. If the size of a field (input string between two   *)
(* comma signs) exceeds 52119 bytes, then the program will segfault when  *)
(* run under Linux' standard stack size (8192*1024 bytes). It does handle *)
(* close to arbitrarily large files however, only the size of the field   *)
(* is a practical issue. *)

(* ****** ****** ****** *)

#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"
staload SBF = "libats/SATS/stringbuf.sats"
staload _(*SBF*) = "libats/DATS/stringbuf.dats"

(* ****** ****** ****** *)

(* The type of a successfully parsed field. *)
typedef 
CSVField = @{ 
  csvRowNum = int,
  csvColNum = int,
  csvTextStart = (int, int),
  csvTextEnd = (int, int),
  csvFieldContent = string,
  csvFieldQuoted = bool
} 

(* A malformed field is parsed to an error instead of causing a halt. *)
typedef 
CSVFieldError = @{ 
  csvRowNum = int,
  csvColNum = int,
  csvTextStart = (int, int),
  csvTextEnd = (int, int),
  csvFieldError = string 
}
 
datatype
CSVEntry = CSV_Field of CSVField | CSV_FieldError of CSVFieldError

(* The output of parsing is a lazy, linear type list of [CSVEntry]:s. *)
vtypedef
CSVEntries = stream_vt(CSVEntry)

(* Input type of the parser. *)
vtypedef
llstring = stream_vt(char) (* "linear, lazy strings" *)

(* The function [lex_csv] is our algorithm for parsing CSV. It depends on
 * two auxiliary variables that are passed by templates. The variable
 * [QNLIN: bool] asserts wether quoted newline characters are considered 
 * admissible ([true]) or not ([false]). The variable [DELIM: char] specifies
 * the chosen field delimiter. Common choices are comma, semicolon or tab. 
 * The variable [cs: llstring] designates the input to be parsed. 
 *)
extern fun {} 
lex_csv(cs: llstring): CSVEntries 

extern fun {}
lex_csv$QNLIN(): bool
extern fun {}
lex_csv$DELIM(): char

(* Default values, to be reimplemented by as needed. *)
implement {}
lex_csv$QNLIN() = false
implement {}
lex_csv$DELIM() = ',' 

(* Reading CSV data is essentially lexical, and can be implemented with a
 * simple finite state machine. We keep track of logical row number,
 * logical column number (in tabular terms), and textual position (row, col)
 * to enable good error messages. Positional data is retained even after 
 * successful lexing, in case a second-stage field parser (work in progress!) 
 * wants to complain. 
 *)
(* Some unnecessary boilerplate to get nice "dot notation" syntax: *) 
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

vtypedef (* Auxiliary buffer type used during parsing. *)
stringbuf = $SBF.stringbuf

implement {}
lex_csv(cs) =
let
  
  fn {}(* Constructs a successfully parsed field. *)
  mk_field ( 
    st: !CSVState >> _,
    at: (int, int),
    acc: !stringbuf,
    p: bool
  ) : CSVEntry =
  CSV_Field @{ 
    csvRowNum = st.tableRow(),
    csvColNum = st.tableCol(),
    csvTextStart = at,
    csvTextEnd = (st.textRow(), st.textCol()),
    csvFieldContent = entrytext,
    csvFieldQuoted = p
  }
  where 
    val entrytext = 
      strptr2string($SBF.stringbuf_takeout_all(acc))
  end
  
  fn {} (* To record an error when parser is fed malformed input. *)
  mk_error ( 
    st: !CSVState >> _,
    at: (int, int),
    txt: string
  ) : CSVEntry =
  CSV_FieldError @{ 
    csvRowNum = st.tableRow(),
    csvColNum = st.tableCol(),
    csvTextStart = at,
    csvTextEnd = (st.textRow(), st.textCol()),
    csvFieldError = txt
  }
  
  (* Some definitions to ease up notation. *)
  #define nil stream_vt_nil
  #define empty stream_vt_make_nil (* "Lazy nil." *)
  #define :: stream_vt_cons

  val NLINE = '\n'
  and CARET = '\r'
  and DQUOT = '"' 
  
  (* The parser is defined by two mutually recursive functions. Briefly, the 
   * function [parse_entry] parses everyting that is not within 
   * double quotes and quoted input is parsed by [parse_string] (below). 
   *)
  fun {} 
  parse_entry (
    st: CSVState,
    at: (int, int),  (* Table position at which to make first entry. *)
    acc: stringbuf,
    cs: llstring
  ) : CSVEntries =
  $ldelay ( 
    case !cs of
    | ~nil() => 
      if $SBF.stringbuf_get_size(acc) = i2sz(0) then ( 
        $SBF.stringbuf_free(acc);
        state_free(st);
        nil()
      )
      else 
        let val field = mk_field(st, at, acc, false)
        in $SBF.stringbuf_free(acc);
           state_free(st);
           field :: empty()
        end 
    | ~(c :: cs1) =>  
      if c = lex_csv$DELIM() then
        case !cs1 of
        | ~(c1 :: cs2) => 
          if c1 = DQUOT then 
            let val new_entry = mk_field(st, at, acc, false)
                val recursive_tail = ( 
                  st.tableCol_inc(1); 
                  st.textCol_inc(2);
                  parse_string(st, (st.textRow(), st.textCol()), acc, cs2)
                )
            in new_entry :: recursive_tail
            end
          else (* [c1 != DQUOT] *)
            let (* [cs1] needs to be recreated. *)
              val new_entry = mk_field(st, at, acc, false)
              val cs1 = stream_vt_make_cons(c1, cs2) 
              val recursive_tail = (
                st.tableCol_inc(1);  
                st.textCol_inc(1);
                parse_entry(st, (st.textRow(), st.textCol()), acc, cs1)
              )
            in new_entry :: recursive_tail
            end
        | ~nil() => 
          let val new_entry = mk_field(st, at, acc, false)
              val recursive_tail = ( 
                st.tableCol_inc(1);  
                st.textCol_inc(1);
                parse_entry(st, (st.textRow(), st.textCol()), acc, empty())
              )
          in new_entry :: recursive_tail
          end
      else if c = CARET then
        case !cs1 of
        | ~(c1 :: cs2) => 
          if c1 = NLINE then 
            let val new_entry = mk_field(st, at, acc, false)
                val recursive_tail = (
                  st.tableRow_inc(1);
                  st.tableCol_set(1);
                  st.textRow_inc(1);
                  st.textCol_set(1);
                  parse_entry(st, (st.textRow(), 1), acc, cs2)
                )
            in new_entry :: recursive_tail
            end
          else (* [c1 != NLINE] *)
            let 
              val new_entry = mk_field(st, at, acc, false)
              val cs1 = stream_vt_make_cons(c1, cs2)
              val recursive_tail = (
                st.tableRow_inc(1);
                st.tableCol_set(1);
                st.textRow_inc(1);
                st.textCol_set(1);
                parse_entry(st, (st.textRow(), 1), acc, cs1)
              )
            in new_entry :: recursive_tail
            end
        | ~nil() => 
          let 
            val new_entry = mk_field(st, at, acc, false)
            val recursive_tail = (
              st.tableRow_inc(1);
              st.tableCol_set(1);
              st.textRow_inc(1);
              st.textCol_set(1);
              parse_entry(st, (st.textRow(), 1), acc, empty())
            )
          in new_entry :: recursive_tail
          end
      else if c = NLINE then
        let val new_entry = mk_field(st, at, acc, false)
            val recursive_tail = (
              st.tableRow_inc(1);
              st.tableCol_set(1);
              st.textRow_inc(1);
              st.textCol_set(1);
              parse_entry(st, (st.textRow(), 1), acc, cs1)
            )
        in new_entry :: recursive_tail
        end
      else if c = DQUOT then
        if $SBF.stringbuf_get_size(acc) = i2sz(0) then (
          st.textCol_inc(1); 
          !(parse_string(st, at, acc, cs1))
        )
        else 
          let val new_entry = mk_error(st, at, "Start-quote next to comma.")
              val recursive_tail = (
                st.textCol_inc(1); 
                parse_string(st, at, acc, cs1)
              )
          in new_entry :: recursive_tail
          end
      else (* When [c] is not special. *) 
        let val c = $UN.cast{charNZ}(c)
        in ignoret($SBF.stringbuf_insert_char(acc, c));
           st.textCol_inc(1);
           !(parse_entry(st, at, acc, cs1))
        end (* [stringbuf_insert_char: int], but [acc] is updated. *)  
    ,    
    ($SBF.stringbuf_free(acc); state_free(st); $effmask_wrt(~cs))
  )
  
  and  
  parse_string (
    st: CSVState,
    at: (int, int),
    acc: stringbuf,
    cs: llstring
  ) : CSVEntries = 
  $ldelay (
    case !cs of
    | ~nil() => 
      if $SBF.stringbuf_get_size(acc) = i2sz(0) then 
        let val field = mk_error(st, at, "Data ends at start-quote.")
        in $SBF.stringbuf_free(acc);
           state_free(st);
           field :: empty()
        end
      else 
        let val field = mk_error(st, at, "Data ends inside quoted field.")
        in $SBF.stringbuf_free(acc);
           state_free(st);
           field :: empty()
        end
    | ~(c :: cs1) =>
      if c = DQUOT then
        case !cs1 of
        | ~nil() => 
          let val field = mk_field(st, at, acc, true)
          in $SBF.stringbuf_free(acc);
             state_free(st);
             field :: empty()
          end
        | ~(c1 :: cs2) =>
          case !cs2 of
          | ~(c2 :: cs3) =>
            if c1 = DQUOT then
              let val cs2 = stream_vt_make_cons(c2, cs3)
                  val dquot = $UN.cast{charNZ}(DQUOT)
              in ignoret($SBF.stringbuf_insert_char(acc, dquot));
                 st.tableCol_inc(1);
                 st.textCol_inc(1);
                 !(parse_string(st, at, acc, cs2))
              end
            else if (c1 = lex_csv$DELIM()) && (c2 = DQUOT) then
              let val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.tableCol_inc(2); 
                    st.textCol_inc(2);
                    parse_string(st, (st.textRow(), st.textCol()), acc, cs3)
                  )
              in new_entry :: recursive_tail
              end
            else if c1 = lex_csv$DELIM() then
              let val cs2 = stream_vt_make_cons(c2, cs3)
                  val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.tableCol_inc(1);
                    st.textCol_inc(2);
                    parse_entry(st, (st.textRow(), st.textCol()), acc, cs2)
                  )
              in new_entry :: recursive_tail
              end
            else if c1 = NLINE then
              let val cs2 = stream_vt_make_cons(c2, cs3)
                  val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.tableRow_inc(1);
                    st.tableCol_set(1); 
                    st.textRow_inc(1);
                    st.textCol_set(1);
                    parse_entry(st, (st.textRow(), 1), acc, cs2)
                  )
              in new_entry :: recursive_tail
              end
            else if (c1 = CARET) && (c2 = NLINE) then
              let val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.tableRow_inc(1);
                    st.tableCol_set(1); 
                    st.textRow_inc(1);
                    st.textCol_set(1);
                    parse_entry(st, (st.textRow(), 1), acc, cs3)
                  )
              in new_entry :: recursive_tail
              end
            else
              let val cs1 = stream_vt_make_cons(c1, stream_vt_make_cons(c2, cs3))
                  val new_entry = 
                      mk_error(st, at, "End-quote not followed by comma.")
                  val recursive_tail = (
                    st.textCol_inc(1);
                    parse_entry(st, at, acc, cs1);
                  )
              in new_entry :: recursive_tail
              end
          | ~nil() (* [cs2 = empty()] *) =>
            if c1 = DQUOT then
              let val dquot = $UN.cast{charNZ}(DQUOT)
              in ignoret($SBF.stringbuf_insert_char(acc, dquot));
                 st.tableCol_inc(1);
                 st.textCol_inc(1);
                 !(parse_string(st, at, acc, empty()))
              end
            else if c1 = lex_csv$DELIM() then
              let val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.tableCol_inc(1);
                    st.textCol_inc(2);
                    parse_entry(st, (st.textRow(), st.textCol()), acc, empty())
                  )
              in new_entry :: recursive_tail
              end
            else if c1 = NLINE then
              let val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.tableRow_inc(1);
                    st.tableCol_set(1); 
                    st.textRow_inc(1);
                    st.textCol_set(1);
                    parse_entry(st, (st.textRow(), 1), acc, empty())
                  )
              in new_entry :: recursive_tail
              end
            else (* cs = cons(DQUOT, sing(c1)), c1 not interesting. *)  
              let val cs1 = stream_vt_make_sing(c1)
                  val new_entry = 
                      mk_error(st, at, "End-quote not followed by comma.")
                  val recursive_tail = (
                    st.textCol_inc(1); 
                    parse_entry(st, at, acc, cs1)
                  )
              in new_entry :: recursive_tail
              end
      else if c = CARET then
        case !cs1 of
        | ~(c1 :: cs2) =>
          if c1 = NLINE then
            if lex_csv$QNLIN() then
              let val nline = $UN.cast{charNZ}(NLINE)
              in ignoret($SBF.stringbuf_insert_char(acc, nline));
                 st.textRow_inc(1);
                 st.textCol_set(1);
                 !(parse_string(st, at, acc, cs2))
              end
            else 
              let val new_entry = mk_error(st, at, "Newline within quoted field.")
                  val recursive_tail = (
                    st.tableRow_inc(1);
                    st.tableCol_set(1); 
                    st.textRow_inc(1);
                    st.textCol_set(1);
                    $SBF.stringbuf_remove_all(acc);
                    parse_entry(st, (st.textRow(), st.textCol()), acc, cs2)
                  )
               in new_entry :: recursive_tail
               end
          else
            let val cs1 = stream_vt_make_cons(c1, cs2)
                val caret = $UN.cast{charNZ}(CARET)
            in ignoret($SBF.stringbuf_insert_char(acc, caret));
               st.textCol_inc(1);
               !(parse_string(st, at, acc, cs1))
            end
        | ~nil() =>
          let val caret = $UN.cast{charNZ}(CARET)
          in ignoret($SBF.stringbuf_insert_char(acc, caret));
             st.textCol_inc(1);
             !(parse_string(st, at, acc, empty()))
          end
      else if c = NLINE then
        if lex_csv$QNLIN() then
          let val nline = $UN.cast{charNZ}(NLINE)
          in ignoret($SBF.stringbuf_insert_char(acc, nline));
             st.textRow_inc(1);
             st.textCol_set(1);
             !(parse_string(st, at, acc, cs1))
          end
        else 
          let val new_entry = mk_error(st, at, "Newline within quoted field.")
              val recursive_tail = (
                st.tableRow_inc(1);
                st.tableCol_set(1); 
                st.textRow_inc(1);
                st.textCol_set(1);
                $SBF.stringbuf_remove_all(acc);
                parse_entry(st, (st.textRow(), 1), acc, cs1)
              )
           in new_entry :: recursive_tail
           end
      else (* [c] not an interesting character. *) 
        let val cnz = $UN.cast{charNZ}(c)
        in ignoret($SBF.stringbuf_insert_char(acc, cnz));
           st.textCol_inc(1);
           !(parse_string(st, at, acc, cs1))
        end, 
    ($SBF.stringbuf_free(acc); state_free(st); $effmask_wrt(~cs))
  )
  
  val initial_state = state_init(1, 1, 1, 1)
  val start_at = (1, 1)
  val empty_sbf = $SBF.stringbuf_make_nil_int(512)
  val result = parse_entry(initial_state, start_at, empty_sbf, cs)
in 
  result
end (* of [implement lex_csv] *)

(* Example main-function to show some functionality. *)
implement main0 () = { 
  val inp = fileref_open_exn("data.csv", file_mode_r)
  val ins = streamize_fileref_char(inp)
  implement {} lex_csv$DELIM() = ';' (* Reimplement delimiter. *)
  val lexed = lex_csv(ins)

  fun
  print_csvFieldContents(es: CSVEntries): void =
  case !es of
  | ~stream_vt_nil() => ()
  | ~stream_vt_cons(e, es1) =>
    let val- CSV_Field(r) = e (* OK if no malformed input. *)
        val s = r.csvFieldContent
    in (print(s); print(", "); print_csvFieldContents(es1))
    end
  
  val () = print_csvFieldContents(lexed)
  val () = fileref_close(inp)
}
