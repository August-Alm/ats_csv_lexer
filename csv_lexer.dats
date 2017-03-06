(* This program parses CSV data conforming to the RFC 4180 standard.     *) 
(* The algorithm uses the same over-arching logic as the Haskell package *)
(* "lazy-csv" but makes significant use of features unique to ATS.       *)

(* ****** ****** ****** *)

#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"
staload SBF = "libats/SATS/stringbuf.sats"
staload _(*SBF*) = "libats/DATS/stringbuf.dats"

(* ****** ****** ****** *)

typedef
CSVField = @{ 
  csvRowNum = int,
  csvColNum = int,
  csvTextStart = (int, int),
  csvTextEnd = (int, int),
  csvFieldContent = string,
  csvFieldQuoted = bool
} 

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

vtypedef
CSVEntries = stream_vt(CSVEntry)

vtypedef
llstring = stream_vt(char) (* linear, lazy strings *)

vtypedef 
stringbuf = $SBF.stringbuf

(* The function [lex_csv] is our algorithm for parsing CSV. The variable
 * [QNLIN: bool] asserts wether quoted newline characters are considered 
 * admissible ([true]) or not ([false]). The variable [DELIM: char] specifies
 * the chosen field delimiter. Common choices are comma, semicolon or tab. 
 * The variable [cs: llstring] designates the input to be parsed. 
 *)
extern fun 
lex_csv(QNLIN: bool, DELIM: char, cs: llstring): CSVEntries 

(* Reading CSV data is essentially lexical, and can be implemented with a
 * simple finite state machine. We keep track of logical row number,
 * logical column number (in tabular terms), and textual position (row, col)
 * to enable good error messages. Positional data is retained even after 
 * successful lexing, in case a second-stage field parser (work in progress!) 
 * wants to complain. 
 *)
local 
  typedef 
  CSVState_rec = @{ 
    tableRow = int,
    tableCol = int,
    textRow = int,
    textCol = int 
  }
in 
  vtypedef
  CSVState = [L: addr] (CSVState_rec@L, mfree_gc_v(L)| ptr(L))

  fun
  state_free(st: CSVState): void =
  ptr_free{CSVState_rec}(st.1, st.0| st.2)
  
  fun 
  state_init(i: int, j: int, k: int, l: int): CSVState =
  let val (pfat, pfgc| p) = ptr_alloc<CSVState_rec?>()
  in p->tableRow := i; 
     p->tableCol := j;
     p->textRow := k;
     p->textCol := l;
     (pfat, pfgc| p) 
  end
end 

implement 
lex_csv(QNLIN, DELIM, cs) =
let
  
  fn
  mk_field ( 
    st: !CSVState >> _,
    at: (int, int),
    acc: !stringbuf,
    p: bool
  ) : CSVEntry =
  CSV_Field @{ 
    csvRowNum = st.2->tableRow,
    csvColNum = st.2->tableCol,
    csvTextStart = at,
    csvTextEnd = (st.2->textRow, st.2->textCol),
    csvFieldContent = entrytext,
    csvFieldQuoted = p
  }
  where 
    val entrytext = 
      strptr2string($SBF.stringbuf_takeout_all(acc))
  end
  
  fn
  mk_error ( 
    st: !CSVState >> _,
    at: (int, int),
    txt: string
  ) : CSVEntry =
  CSV_FieldError @{ 
    csvRowNum = st.2->tableRow,
    csvColNum = st.2->tableCol,
    csvTextStart = at,
    csvTextEnd = (st.2->textRow, st.2->textCol),
    csvFieldError = txt
  }
  
  (* Some definitions to ease up notation. *)
  #define nil stream_vt_nil
  #define empty stream_vt_make_nil (* "Lazy nil." *)
  #define :: stream_vt_cons
  val NLINE = '\n'
  and CARET = '\r'
  and DQUOT = '"'  
  
  fun 
  parse_entry (
    st: CSVState,
    at: (int, int),  (* Table position at which to make entry. *)
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
      if c = DELIM then
        case !cs1 of
        | ~(c1 :: cs2) => 
          if c1 = DQUOT then 
            let val new_entry = mk_field(st, at, acc, false)
                val recursive_tail = ( 
                  st.2->tableCol := st.2->tableCol + 1; 
                  st.2->textCol := st.2->textCol + 2;
                  parse_string(st, (st.2->textRow, st.2->textCol), acc, cs2)
                )
            in new_entry :: recursive_tail
            end
          else (* [c1 != DQUOT] *)
            let (* [cs1] needs to be recreated. *)
              val new_entry = mk_field(st, at, acc, false)
              val cs1 = stream_vt_make_cons(c1, cs2) 
              val recursive_tail = (
                st.2->tableCol := st.2->tableCol + 1;  
                st.2->textCol := st.2->textCol + 1;
                parse_entry(st, (st.2->textRow, st.2->textCol), acc, cs1)
              )
            in new_entry :: recursive_tail
            end
        | ~nil() => 
          let val new_entry = mk_field(st, at, acc, false)
              val recursive_tail = ( 
                st.2->tableCol := st.2->tableCol + 1;  
                st.2->textCol := st.2->textCol + 1;
                parse_entry(st, (st.2->textRow, st.2->textCol), acc, empty())
              )
          in new_entry :: recursive_tail
          end
      else if c = CARET then
        case !cs1 of
        | ~(c1 :: cs2) => 
          if c1 = NLINE then 
            let val new_entry = mk_field(st, at, acc, false)
                val recursive_tail = (
                  st.2->tableCol := 1; 
                  st.2->textCol := 1;
                  st.2->tableRow := st.2->tableRow + 1;  
                  st.2->textRow := st.2->textRow + 1;
                  parse_entry(st, (st.2->textRow, 1), acc, cs2)
                )
            in new_entry :: recursive_tail
            end
          else (* [c1 != NLINE] *)
            let 
              val new_entry = mk_field(st, at, acc, false)
              val cs1 = stream_vt_make_cons(c1, cs2)
              val recursive_tail = (
                st.2->tableCol := 1; 
                st.2->textCol := 1;
                st.2->tableRow := st.2->tableRow + 1; 
                st.2->textRow := st.2->textRow + 1;
                parse_entry(st, (st.2->textRow, 1), acc, cs1)
              )
            in new_entry :: recursive_tail
            end
        | ~nil() => 
          let 
            val new_entry = mk_field(st, at, acc, false)
            val recursive_tail = (
              st.2->tableCol := 1; 
              st.2->textCol := 1;
              st.2->tableRow := st.2->tableRow + 1;  
              st.2->textRow := st.2->textRow + 1;
              parse_entry(st, (st.2->textRow, 1), acc, empty())
            )
          in new_entry :: recursive_tail
          end
      else if c = NLINE then
        let val new_entry = mk_field(st, at, acc, false)
            val recursive_tail = (
              st.2->tableCol := 1; 
              st.2->textCol := 1;
              st.2->tableRow := st.2->tableRow + 1;  
              st.2->textRow := st.2->textRow + 1;
              parse_entry(st, (st.2->textRow, 1), acc, cs1)
            )
        in new_entry :: recursive_tail
        end
      else if c = DQUOT then
        if $SBF.stringbuf_get_size(acc) = i2sz(0) then ( 
          st.2->textCol := st.2->textCol + 1;
          !(parse_string(st, at, acc, cs1))
        )
        else 
          let val new_entry = mk_error(st, at, "Start-quote next to comma.")
              val recursive_tail = (
                st.2->textCol := st.2->textCol + 1; 
                parse_string(st, at, acc, cs1)
              )
          in new_entry :: recursive_tail
          end
      else (* When [c] is not special. *) 
        let val c = $UN.cast{charNZ}(c)
        in ignoret($SBF.stringbuf_insert_char(acc, c));
           st.2->textCol := st.2->textCol + 1;
           !(parse_entry(st, at, acc, cs1))
        end, (* [stringbuf_insert_char: int], but [acc] is updated. *)  
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
                 st.2->tableCol := st.2->tableCol + 1;
                 st.2->textCol := st.2->textCol + 1;
                 !(parse_string(st, at, acc, cs2))
              end
            else if (c1 = DELIM) && (c2 = DQUOT) then
              let val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.2->tableCol := st.2->tableCol + 2; 
                    st.2->textCol := st.2->textCol + 2;
                    parse_string(st, (st.2->textRow, st.2->textCol), acc, cs3)
                  )
              in new_entry :: recursive_tail
              end
            else if c1 = DELIM then
              let val cs2 = stream_vt_make_cons(c2, cs3)
                  val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.2->tableCol := st.2->tableCol + 1;
                    st.2->textCol := st.2->textCol + 2;
                    parse_entry(st, (st.2->textRow, st.2->textCol), acc, cs2)
                  )
              in new_entry :: recursive_tail
              end
            else if c1 = NLINE then
              let val cs2 = stream_vt_make_cons(c2, cs3)
                  val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.2->tableCol := 1; 
                    st.2->textCol := 1;
                    st.2->tableRow := st.2->tableRow + 1;
                    st.2->textRow := st.2->textRow + 1;
                    parse_entry(st, (st.2->textRow, 1), acc, cs2)
                  )
              in new_entry :: recursive_tail
              end
            else if (c1 = CARET) && (c2 = NLINE) then
              let val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.2->tableCol := 1;
                    st.2->textCol := 1;
                    st.2->tableRow := st.2->tableRow + 1;
                    st.2->textRow := st.2->textRow + 1;
                    parse_entry(st, (st.2->textRow, 1), acc, cs3)
                  )
              in new_entry :: recursive_tail
              end
            else
              let val cs1 = stream_vt_make_cons(c1, stream_vt_make_cons(c2, cs3))
                  val new_entry = 
                      mk_error(st, at, "End-quote not followed by comma.")
                  val recursive_tail = (
                    st.2->textCol := st.2->textCol + 1;
                    parse_entry(st, at, acc, cs1);
                  )
              in new_entry :: recursive_tail
              end
          | ~nil() (* [cs2 = empty()] *) =>
            if c1 = DQUOT then
              let val dquot = $UN.cast{charNZ}(DQUOT)
              in ignoret($SBF.stringbuf_insert_char(acc, dquot));
                 st.2->tableCol := st.2->tableCol + 1;
                 st.2->textCol := st.2->textCol + 1;
                 !(parse_string(st, at, acc, empty()))
              end
            else if c1 = DELIM then
              let val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.2->tableCol := st.2->tableCol + 1;
                    st.2->textCol := st.2->textCol + 2;
                    parse_entry(st, (st.2->textRow, st.2->textCol), acc, empty())
                  )
              in new_entry :: recursive_tail
              end
            else if c1 = NLINE then
              let val new_entry = mk_field(st, at, acc, true)
                  val recursive_tail = (
                    st.2->tableCol := 1; 
                    st.2->textCol := 1;
                    st.2->tableRow := st.2->tableRow + 1;
                    st.2->textRow := st.2->textRow + 1;
                    parse_entry(st, (st.2->textRow, 1), acc, empty())
                  )
              in new_entry :: recursive_tail
              end
            else (* cs = cons(DQUOT, sing(c1)), c1 not interesting. *)  
              let val cs1 = stream_vt_make_sing(c1)
                  val new_entry = 
                      mk_error(st, at, "End-quote not followed by comma.")
                  val recursive_tail = (
                    st.2->textCol := st.2->textCol + 1; 
                    parse_entry(st, at, acc, cs1)
                  )
              in new_entry :: recursive_tail
              end
      else if c = CARET then
        case !cs1 of
        | ~(c1 :: cs2) =>
          if c1 = NLINE then
            if QNLIN then
              let val nline = $UN.cast{charNZ}(NLINE)
              in ignoret($SBF.stringbuf_insert_char(acc, nline));
                 st.2->textRow := st.2->textRow+1;
                 st.2->textCol := 1;
                 !(parse_string(st, at, acc, cs2))
              end
            else 
              let val new_entry = mk_error(st, at, "Newline within quoted field.")
                  val recursive_tail = (
                    st.2->tableCol := 1;
                    st.2->textCol := 1;
                    st.2->tableRow := st.2->tableRow + 1;
                    st.2->textRow := st.2->textRow + 1;
                    $SBF.stringbuf_remove_all(acc);
                    parse_entry(st, (st.2->textRow, st.2->textCol), acc, cs2)
                  )
               in new_entry :: recursive_tail
               end
          else
            let val cs1 = stream_vt_make_cons(c1, cs2)
                val caret = $UN.cast{charNZ}(CARET)
            in ignoret($SBF.stringbuf_insert_char(acc, caret));
               st.2->textCol := st.2->textCol + 1;
               !(parse_string(st, at, acc, cs1))
            end
        | ~nil() =>
          let val caret = $UN.cast{charNZ}(CARET)
          in ignoret($SBF.stringbuf_insert_char(acc, caret));
             st.2->textCol := st.2->textCol + 1;
             !(parse_string(st, at, acc, empty()))
          end
      else if c = NLINE then
        if QNLIN then
          let val nline = $UN.cast{charNZ}(NLINE)
          in ignoret($SBF.stringbuf_insert_char(acc, nline));
             st.2->textCol := 1;
             st.2->textRow := st.2->textRow + 1;
             !(parse_string(st, at, acc, cs1))
          end
        else 
          let val new_entry = mk_error(st, at, "Newline within quoted field.")
              val recursive_tail = (
                st.2->tableCol := 1;
                st.2->textCol := 1;
                st.2->tableRow := st.2->tableRow + 1;
                st.2->textRow := st.2->textRow + 1;
                $SBF.stringbuf_remove_all(acc);
                parse_entry(st, (st.2->textRow, 1), acc, cs1)
              )
           in new_entry :: recursive_tail
           end
      else (* [c] not an interesting character. *) 
        let val cnz = $UN.cast{charNZ}(c)
        in ignoret($SBF.stringbuf_insert_char(acc, cnz));
           st.2->textCol := st.2->textCol + 1;
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

implement main0 () = { 
  val inp = fileref_open_exn("data.csv", file_mode_r)
  val ins = streamize_fileref_char(inp)
  val lexed = lex_csv(true, ';', ins)
  val h = lexed.head()
  val- CSV_Field(r) = h
  val a = r.csvFieldContent
  val () = println!(a) (* Prints first field to console. *)
  val () = fileref_close(inp) 
}
