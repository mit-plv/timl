structure Util = struct

infixr 0 $
fun f $ x = f x

fun interleave xs ys =
    case xs of
	x :: xs' => x :: interleave ys xs'
      | nil => ys
fun take n ls = if n < 0 then [] else if n > length ls then ls else List.take (ls, n)
fun drop n ls = if n < 0 then ls else if n > length ls then [] else List.drop (ls, n)
fun skip start len ls = take start ls @ drop (start + len) ls
fun remove n ls = skip n 1 ls

fun sprintf s ls =
    String.concat (interleave (String.fields (fn c => c = #"$") s) ls)
fun printf s ls = print $ sprintf s ls
fun println s = print (s ^ "\n")
fun trace s a = (println s; a)

fun default v opt = getOpt (opt, v)
fun lazy_default v opt = 
    case opt of
        SOME a => a
      | NONE => v ()
fun isNull opt = not (isSome opt)

val join = String.concatWith
fun prefix fix s = fix ^ s
fun suffix fix s = s ^ fix
fun surround pre post s = pre ^ s ^ post
fun indent msg = map (fn s => "  " ^ s) msg
fun join_lines ls = (join "" o map (suffix "\n")) ls
fun join_prefix pre ls = (join "" o map (prefix pre)) ls
                                                      
fun str_ls f ls = (surround "[" "]" o join ", " o map f) ls
fun str_pair (f, g) (a, b) = sprintf "($, $)" [f a, g b]
fun str_opt f opt = (default "" o Option.map f) opt
val str_int = Int.toString
fun str_bool b = if b then "true" else "false"

fun id x = x
fun const a _ = a
fun range n = List.tabulate (n, id)
fun repeat n a = List.tabulate (n, const a)
                               
fun nth_error ls n =
    if n < 0 orelse n >= length ls then
      NONE
    else
      SOME (List.nth (ls, n))

fun fst (a, b) = a
fun snd (a, b) = b
fun mapFst f (a, b) = (f a, b)
fun mapSnd f (a, b) = (a, f b)
fun mapPair (fa, fb) (a, b) = (fa a, fb b)
fun curry f a b = f (a, b)
fun uncurry f (a, b) = f a b
fun swap f (a, b) = f (b, a)
fun flip f a b = f b a
fun upd4 f (a, b, c, d) = (a, b, c, f d)

(* fun add_idx ls = ListPair.zip (range (length ls), ls) *)

fun findWithIdx f xs =
    let
      fun loop base xs =
          case xs of
              [] => NONE
            | x :: xs =>
              if f (base, x) then
                SOME (base, x)
              else
                loop (base + 1) xs
    in
      loop 0 xs
    end
      
fun findOptionWithIdx f xs =
    let
      fun loop base xs =
          case xs of
              [] => NONE
            | x :: xs =>
              case f (base, x) of
                  SOME a =>
                  SOME a
                | NONE =>
                  loop (base + 1) xs
    in
      loop 0 xs
    end
      
fun mapPartialWithIdx f xs =
    let
      fun iter (x, (n, acc)) =
          let
            val acc =
                case f (n, x) of
                    SOME b => (n, b) :: acc
                  | NONE => acc
          in
            (n + 1, acc)
          end
    in
      rev $ snd $ foldl iter (0, []) xs
    end
      
datatype ('a, 'b) result =
	 OK of 'a
	 | Failed of 'b

val zip = ListPair.zip
val unzip = ListPair.unzip

fun allSome f (xs : 'a list) =
    let
      exception Error of int * 'a
      fun iter (x, (n, acc)) =
          let
            val acc =
                case f x of
                    SOME y => y :: acc
                  | NONE => raise Error (n, x)
          in
            (n + 1, acc)
          end
      val ret = OK $ rev $ snd $ foldl iter (0, []) xs
                handle Error e => Failed e
    in
      ret
    end

fun to_hd i l = List.nth (l, i) :: take i l @ drop (i + 1) l

exception Impossible of string

fun singleton x = [x]
fun mem eq x ls = List.exists (fn y => eq (y, x)) ls
fun subset eq a b =
    List.all (fn x => mem eq x b) a
fun diff eq a b = List.filter (fn x => not (mem eq x b)) a
fun dedup eq xs =
    case xs of
        [] => []
      | x :: xs => x :: dedup eq (diff eq xs [x])

fun foldl' f init xs =
    case xs of
        [] => init
      | x :: xs => foldl f x xs

fun max a b = if a < b then b else a

fun write_file (filename, s) =
    let
      val out =  TextIO.openOut filename
      val () = TextIO.output (out, s)
      val () = TextIO.closeOut out
    in
      ()
    end

fun read_file filename =
    let
      val ins = TextIO.openIn filename
      val s = TextIO.input ins
      val _ = TextIO.closeIn ins
    in
      s
    end
      
fun read_lines filename =
    let
      open TextIO
      val ins = openIn filename
      fun loop lines =
          case inputLine ins of
              SOME ln => loop (String.substring (ln, 0, String.size ln - 1) :: lines)
            | NONE => lines
      val lines = rev $ loop []
      val () = closeIn ins
    in
      lines
    end
      
fun trim s =
    let
      fun first_non_space s =
          let
            val len = String.size s
            fun loop n =
                if n >= len then
                  NONE
                else
                  if Char.isSpace $ String.sub (s, n)  then
                    loop (n + 1)
                  else
                    SOME n
          in
            loop 0
          end
      fun last_non_space s =
          let
            val len = String.size s
            fun loop n =
                if n < 0 then
                  NONE
                else
                  if Char.isSpace $ String.sub (s, n)  then
                    loop (n - 1)
                  else
                    SOME n
          in
            loop (len - 1)
          end
      val first = first_non_space s
      val last = last_non_space s
    in
      case (first, last) of
          (SOME first, SOME last) =>
          if first <= last then
            String.substring (s, first, last - first + 1)
          else
            ""
        | _ => ""
    end
      
fun concatMap f ls = (List.concat o map f) ls

fun inc r = r := !r + 1
fun dec r = r := !r - 1

structure Range = struct

type range = int * int

fun zero_to length = (0, length)

fun foldl f init (start, len) =
    if len <= 0 then
      init
    else
      foldl f (f (start, init)) (start + 1, len - 1)

fun for f init range = foldl f init range

fun app f range = foldl (fn (i, ()) => (f i; ())) () range

end

fun repeat_app f n = Range.app (fn _ => f ()) (Range.zero_to n)

(* uninhabited *)
datatype empty = Empty of empty
fun exfalso (x : empty) = raise Impossible "type empty shouldn't have inhabitant"

fun push xs x = x :: xs
fun binop_ref f r x = r := f (!r) x
fun push_ref r x = binop_ref push r x

datatype ('a, 'b) sum = 
         inl of 'a
         | inr of 'b

fun find_by_snd p ls =
    Option.map fst (List.find (fn (_, y) => p y) ls)
fun find_by_snd_eq eq x ls = find_by_snd (curry eq x) ls
                                         
fun findOption f xs =
    case xs of
        [] => NONE
      | x :: xs =>
        case f x of
            SOME y => SOME y
          | NONE => findOption f xs
                               
fun partitionOption f xs =
    case xs of
        [] => ([], [])
      | x :: xs =>
        let
          val (ys, zs) = partitionOption f xs
        in
          case f x of
              SOME y => (y :: ys, zs)
            | _ => (ys, x :: zs)
        end

fun partitionOptionFirst f xs =
    case xs of
        [] => NONE
      | x :: xs =>
        case f x of
            SOME y => SOME (y, xs)
          | _ =>
            case partitionOptionFirst f xs of
                SOME (a, rest) => SOME (a, x :: rest)
              | NONE => NONE

fun firstSuccess f xs = foldl (fn (x, acc) => case acc of SOME _ => acc | NONE => f x) NONE xs
                              
fun b2o b = if b then SOME () else NONE
                                     
end

