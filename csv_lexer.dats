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

// DOES NOT PASS COMPILATION!!! (FIX IN PROGRESS.)

(* ****** ****** ****** *)

#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"
staload SBF = "libats/SATS/stringbuf.sats"
staload _(*SBF*) = "libats/DATS/stringbuf.dats"

(* The implementation of a number of functions that are simple and short 
 * but not included in the standard ATS libraries is deferred to a separate 
 * file, "csv_lib.hats", to keep the present file transparent.
 *)
#include "csv_lib.hats"

(* ****** FIRST STAGE PARSER ****** *)

(* The type of a successfully (first stage) parsed field. *)
typedef CSVField = @{ 
  csvRowNum = int,
  csvColNum = int,
  csvTextStart = (int, int),
  csvTextEnd = (int, int),
  csvFieldContent = string,
  csvFieldQuoted = bool
} 

(* A malformed field is parsed to an error instead of causing a halt. *)
typedef CSVFieldError = @{ 
  csvRowNum = int,
  csvColNum = int,
  csvTextStart = (int, int),
  csvTextEnd = (int, int),
  csvFieldError = string 
}
 
datatype CSVEntry = CSV_Field of CSVField | CSV_FieldError of CSVFieldError

(* The output of first stage parsing is a lazy, linear list of [CSVEntry]:s. *)
vtypedef CSVEntries = stream_vt(CSVEntry)

(* Input type of the first stage parser. *)
vtypedef llstring = stream_vt(char) (* "linear, lazy strings" *)

(* The function [lex_csv] is our algorithm for first-stage parsing CSV. It  
 * depends on two auxiliary variables passed by templates. The variable
 * [QNLIN: bool] asserts wether quoted newline characters are considered 
 * admissible ([true]) or not ([false]). The variable [DELIM: char] specifies
 * the chosen field delimiter. Common choices are comma, semicolon or tab. 
 * The variable [cs: llstring] designates the input to be parsed. 
 *)
extern fun {} lex_csv(cs: llstring): CSVEntries 

extern fun {} lex_csv$QNLIN(): bool
extern fun {} lex_csv$DELIM(): char

(* Default values, to be reimplemented by user as needed. *)
implement {} lex_csv$QNLIN() = false
implement {} lex_csv$DELIM() = ',' 

(* ****** SECOND STAGE PARSER ****** *)

(* The second stage parser essentially collects the output of the first 
 * stage parser [csv_lexer] into a tabular format, while also checking
 * for "global" errors in the intput data, such as unequal number of columns 
 * in each row.
 *)

(* Templates do not play well with dependent types, so rather than use the
 * dependent type 
 *   List0_vt(a) = [n: int| n >= 0] list_vt(a, n)
 * in a definition, we use it as an "assumption" (which is "reassumed" when
 * needed) on an abstract definition.
 *
 * The (assumed) type [CSVRow] differs from [CSVEntries] in that it is not lazy. 
 *)
absvtype CSVRow 
local assume CSVRow = List0_vt(CSVEntry) in (* nothing *) end

vtypedef CSVTable = stream_vt(CSVRow)        

(* Second stage parsing records more detailed error data. *)
datatype CSVError = 
  | Incorrect_Row of @{ 
      csvRow = int,
      csvColsExpected = int,
      csvColsActual = int,
      csvEntries = List0(CSVEntry) (* Not linear! *)
    } 
  | Blank_Line of @{ 
      csvRow = int,
      csvColsExpected = int,
      csvColsActual = int,
      csvField = CSVField
    } 
  | Field_Error of @{ 
      csvEntry = CSVEntry 
    } 
  | No_Data of () 

absvtype CSVErrors
local assume CSVErrors = List0_vt(CSVError) in (* nothing *) end
(* The [Either] datatype constructor, familiar to all Haskell programmers, 
 * is not in any standard ATS library. A term of type [Either(a, b)] is either 
 * a [Left] value (an [a]) or a [Right] value (a [b]). We implement the
 * [Either] constructor (for linear types [a] and [b]) in "csv_lib.hats", as
 * well as some functions involving it. We use this constructor to define the
 * output type of the second stage parser, as a result is either an error or
 * a regular field.
 *)
vtypedef CSVResult = stream_vt(Either(CSVErrors, CSVRow))

(* "csv_lib.hats" makes use of a template [extfree] to free [Left] and [Right]
 * values.
 *)
implement extfree<CSVErrors>(errs) = list_vt_free(errs)
  where reassume CSVErrors end (* [= List0_vt(CSVError)] *)

implement extfree<CSVRow>(r) = list_vt_free(r)  
  where reassume CSVRow end (* [= List0_vt(CSVEntry)] *)

implement extfree<Either(CSVErrors, CSVRow)>(z) = 
  case z of
  | ~Left(errs) => extfree<CSVErrors>(errs)
  | ~Right(r) => extfree<CSVRow>(r)

(* Our second stage parser: *)
extern fun {} parse_csv(cs: llstring): CSVResult

(* From a [CSVResult] one can filter/project out to only the [Right] or to
 * the [Left] values. In practice one might use [csv_table] (below) directly,
 * rather than [csv_parser].
 *)
fun {} csv_table(cs: llstring): CSVTable = map_right(parse_csv(cs))
  where reassume CSVRow reassume CSVErrors end

fun{} csv_errors(cs: llstring): stream_vt(CSVErrors) = map_left(parse_csv(cs))
  where reassume CSVRow reassume CSVErrors end

(* ****** IMPLEMENT [csv_lexer] ****** *)

(* Reading CSV data is essentially lexical, and can be implemented with a
 * simple finite state machine. We keep track of logical row number,
 * logical column number (in tabular terms), and textual position (row, col)
 * to enable good error messages. Positional data is retained even after 
 * successful lexing, in case a second-stage field parser (work in progress!) 
 * wants to complain. 
 *
 * The "state" in our code is a dateviewtype defined as 
 * datavtype 
 * CSVState = CSV_State of @{
 *   tableRow = int, tableCol = int, textRow = int, textCol = int
 * }
 * 
 * The definition is deferred to "csv_lib.hats" because in addition to just
 * defining the type we also implement some boilerplate so as to get a
 * simple dot-notation syntax, which will let us update a state variable [st]
 * by writing, e.g., [st.textRow_inc(4)].
 *)
(* Auxiliary buffer type used during parsing. *)
vtypedef stringbuf = $SBF.stringbuf

implement {} lex_csv(cs) =
let

  (* Constructs a successfully parsed field. *)
  fn {} mk_field ( 
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
  
  (* To record an error when parser is fed malformed input. *)
  fun {} mk_error ( 
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
  
  (* Some definitions to ease up notation, included in "csv_lib.hats". 
   * #define nil stream_vt_nil
   * #define empty stream_vt_make_nil (* "Lazy nil." *)
   * #define :: stream_vt_cons
   *)
  val NLINE = '\n'
  and CARET = '\r'
  and DQUOT = '"' (* " *) 
  
  (* The parser is defined by two mutually recursive functions. Briefly, the 
   * function [parse_entry] parses everyting that is not within 
   * double quotes and quoted input is parsed by [parse_string] (below). 
   *)
  fun {} parse_entry (
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
  
  and parse_string (
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
                let val cs1 = stream_vt_make_cons
                                (c1, stream_vt_make_cons(c2, cs3))
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
                      parse_entry
                        (st, (st.textRow(), st.textCol()), acc, empty())
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
                let val new_entry = mk_error
                                      (st, at, "Newline within quoted field.")
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

(* ****** IMPLEMENTATION OF [csv_parser] ****** *)

(* A function for later grouping into tabular format based on row number. *)
fn {} eq_csvRowNum(e: CSVEntry): (CSVEntry -<cloref> bool) = 
  lam(e1) =<cloref> case (e, e1) of
  | (CSV_Field(f), CSV_Field(f1)) => 
    let val n = f.csvRowNum and n1 = f1.csvRowNum in n = n1 
    end
  | (CSV_Field(f), CSV_FieldError(f1)) => 
    let val n = f.csvRowNum and n1 = f1.csvRowNum in n = n1
    end
  | (CSV_FieldError(f), CSV_Field(f1)) => 
    let val n = f.csvRowNum and n1 = f1.csvRowNum in n = n1
    end
  | (CSV_FieldError(f), CSV_FieldError(f1)) => 
    let val n = f.csvRowNum and n1 = f1.csvRowNum in n = n1 
    end

(* The function [stream_vt_group_by] is implemented in "csv_lib.hats". If  
 * the extra error checking of the second stage parsing is thought irrelevant,
 * then one may consider using [lex_csv_tabular] (below) as the final 
 * parsing. This function has somewhat better performance than the complete 
 * second stage parser [csv_parser].
 *)
fun {} lex_csv_tabular(cs: llstring): CSVTable = 
  stream_vt_group_by(lex_csv(cs), eq_csvRowNum)
  where reassume CSVRow end

(* The implementation of [csv_parser] is as a composite of [lex_csv_tabular]
 * and a function [validate] which checks for errors and divides output into 
 * [Either] type. 
 *)
extern fun {} validate(rs: CSVTable): CSVResult

implement {} parse_csv(cs) = validate(lex_csv_tabular(cs))
  where reassume CSVRow end

(* The rest of this section is the implementation of [validate]. *)
extern fun {} current_length(): int

extern fun {} extract_errs(r: CSVRow): Either(CSVErrors, CSVRow)

implement {} validate(rs: CSVTable): CSVResult = let
    reassume CSVRow
    reassume CSVErrors
  in
    $ldelay(
      case !rs of
      | ~nil() => let
          val nodata = list_vt_make_sing<CSVError>(No_Data())
        in Left(nodata) :: empty()
        end
      | ~stream_vt_cons(r, rs1) => let 
          val length_r = list_vt_length(r)
          implement {} current_length() = length_r
        in extract_errs(r) :: stream_vt_usermap(rs1, extract_errs)
        end
      ,
      ~rs
    )
  end

(* Implementation of [extract_errs]: *)
local
  fn {} is_field(e: CSVEntry): bool = case e of | CSV_Field(f) => true
                                                | _ => false
  
  fn {} is_empty_field(e_opt: !Option_vt(CSVEntry)): bool = 
    case e_opt of
    | None_vt() => false
    | Some_vt(e) => case e of
                    | CSV_FieldError(er) => false
                    | CSV_Field(f) => let val s = f.csvFieldContent 
                                      in string0_length(s) = 0
                                      end
  
  fn {} convert(e: CSVEntry): CSVError = Field_Error @{csvField = e}
  
  (* The functions [list_vt_head_opt] ("safe head") is implemented 
   * in "csv_lib.hats". 
   *)
  fun {} validate_columns(r: CSVRow): CSVErrors = let 
      reassume CSVRow
      reassume CSVErrors
    in let
        val length_r = list_vt_length(r)  
      in if length_r = current_length() then (free(r); list_vt_nil())
         else let 
             val csv_row = if length_r = 0 then 0 
                           else let 
                               val h_opt = list_vt_head_opt<CSVEntry>(r)
                               val- ~Some_vt(e) = h_opt
                             in case e: CSVEntry of
                                | CSV_Field(f) => f.csvRowNum
                                | CSV_FieldError(er) => er.csvRowNum 
                             end
             val list_r = list_vt2t(r)
             val incorrect_row = Incorrect_Row @{
                                   csvRow = csv_row,
                                   csvColsExpected = current_length(),
                                   csvColsActual = length_r,
                                   csvEntries = list_r
                                 }
           in list_vt_sing(incorrect_row)
           end
      end
    end
in (* of local *)
  (* The functions [list_vt_head_opt] and [list_vt_usermap] are implemented
   * in "csv_lib.hats".
   *)
  implement {} extract_errs(r) = let
      reassume CSVRow
      reassume CSVErrors
    in let 
        val (fields, errs) = list_vt_partition<CSVEntry>(r, is_field)
        val ln = list_vt_length<CSVEntry>(fields)
        val h_opt = list_vt_head_opt<CSVEntry>(fields)
      in 
        if ln = current_length() && list_vt_is_nil(errs) 
        then (
          option_vt_free(h_opt); 
          free(errs); 
          Right(fields)
        )
        else if ln = 1 && is_empty_field(h_opt) then   
          let val- Some_vt(e: CSVEntry) = h_opt
              val- CSV_Field(f) = e
              val blank = Blank_Line @{
                csvRow = f.csvRowNum,
                csvColsExpected = current_length(),
                csvColsActual = 1,
                csvField = f
              }
          in (
            option_vt_free(h_opt); 
            free(fields); 
            free(errs); 
            Left(list_vt_sing(blank))
          )
          end 
        else (
          option_vt_free(h_opt); 
          Left(list_vt_usermap(errs, convert) ** validate_columns(fields))
        )
      end
    end
end (* of local *)

(* ****** FUNCTIONS FOR PRINTING ****** *)

fun csv_table_print(rs: CSVTable): void = 
  let
    fun row_print(es: CSVRow): void = let
        reassume CSVRow
      in case es of
         | ~list_vt_nil() => ()
         | ~list_vt_cons(e, es1) => let 
             val- CSV_Field(f) = e (* OK if no [CSV_FieldErrors]. *) 
             val s = f.csvFieldContent
           in (print(s); print(", "); row_print(es1))
           end
      end
  in
    case !rs of
    | ~nil() => print("\n")
    | ~(r :: rs1) => (row_print(r); println!("; "); csv_table_print(rs1))
  end

(* ****** ****** ****** *)

(* Example main-function to show some functionality: *)
implement main0 () = { 
  val inp = fileref_open_exn("artist_data.csv", file_mode_r)
  val ins = streamize_fileref_char(inp)
  implement {} lex_csv$DELIM() = ';' (* Reimplement delimiter. *)
  val table = csv_table(ins)
  val () = csv_table_print(table)
  val () = fileref_close(inp)
}
