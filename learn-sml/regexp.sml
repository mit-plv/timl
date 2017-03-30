signature REGEXP = sig

  datatype regexp =
    Zero | One | Char of char | 
    Plus of regexp * regexp | Times of regexp * regexp |
    Star of regexp

  exception SyntaxError of string
  val parse : string -> regexp

  val format : regexp -> string

end
  
signature MATCHER = sig

  structure RegExp : REGEXP

  val match : RegExp.regexp -> string -> bool

end

structure RegExp :> REGEXP = struct

  datatype token =
    AtSign | Percent | Literal of char | PlusSign | TimesSign |
    Asterisk | LParen | RParen

  exception LexicalError

  fun tokenize nil = nil
    | tokenize (#"+" :: cs) = (PlusSign :: tokenize cs)
    | tokenize (#"." :: cs) = (TimesSign :: tokenize cs)
    | tokenize (#"*" :: cs) = (Asterisk :: tokenize cs)
    | tokenize (#"(" :: cs) = (LParen :: tokenize cs)
    | tokenize (#")" :: cs) = (RParen :: tokenize cs)
    | tokenize (#"@" :: cs) = (AtSign :: tokenize cs)
    | tokenize (#"%" :: cs) = (Percent :: tokenize cs)
    | tokenize (#"\\" :: c :: cs) = Literal c :: tokenize cs
    | tokenize (#"\\" :: nil) = raise LexicalError
    | tokenize (#" " :: cs) = tokenize cs
    | tokenize (c :: cs) = Literal c :: tokenize cs

  datatype regexp =
    Zero | One | Char of char | 
    Plus of regexp * regexp | Times of regexp * regexp |
    Star of regexp

  exception SyntaxError of string

  fun parse_exp ts =
      let
          val (r, ts') = parse_term ts
      in
          case ts'
            of (PlusSign::ts'') =>
               let
                   val (r', ts''') = parse_exp ts''
               in
                   (Plus (r, r'), ts''')
               end
             | _ => (r, ts')
      end

  and parse_term ts =
      let
          val (r, ts') = parse_factor ts
      in
          case ts'
            of (TimesSign::ts'') =>
               let
                   val (r', ts''') = parse_term ts''
               in
                   (Times (r, r'), ts''')
               end
             | _ => (r, ts')
      end

  and parse_factor ts =
      let
          val (r, ts') = parse_atom ts
      in
          case ts'
            of (Asterisk :: ts'') => (Star r, ts'')
             | _ => (r, ts')
      end

  and parse_atom nil = raise SyntaxError ("Factor expected\n")
    | parse_atom (AtSign :: ts) = (Zero, ts)
    | parse_atom (Percent :: ts) = (One, ts)
    | parse_atom ((Literal c) :: ts) = (Char c, ts)
    | parse_atom (LParen :: ts) =
      let
          val (r, ts') = parse_exp ts
      in
          case ts'
            of nil => raise SyntaxError ("Right-parenthesis expected\n")
             | (RParen :: ts'') => (r, ts'')
             | _ => raise SyntaxError ("Right-parenthesis expected\n")
      end
    | parse_atom _ = raise SyntaxError ("Unknown\n")
      
  fun parse s =
      let
          val (r, ts) = parse_exp (tokenize (String.explode s))
      in
          case ts
            of nil => r
             | _ => raise SyntaxError "Unexpected input.\n"
      end
      handle LexicalError => raise SyntaxError "Illegal input.\n"
      
  fun format_exp Zero = [#"@"]
    | format_exp One = [#"%"]
    | format_exp (Char c) = [c]
    | format_exp (Plus (r1, r2)) =
      let
          val s1 = format_exp r1
          val s2 = format_exp r2
      in
          [#"("] @ s1 @ [#"+"] @ s2 @ [#")"]
      end
    | format_exp (Times (r1, r2)) =
      let
          val s1 = format_exp r1
          val s2 = format_exp r2
      in
          s1 @ [#"*"] @ s2
      end
    | format_exp (Star r) =
      let
          val s = format_exp r
      in
          [#"("] @ s @ [#")"] @ [#"*"]
      end

  fun format r = String.implode (format_exp r)

end

structure Matcher :> MATCHER =
struct

    structure RegExp = RegExp
    open RegExp

    fun match' Zero _ k = false
      | match' One cs k = k cs
      | match' (Char c) cs k =
	(case cs of nil => false | c'::cs' => (c=c') andalso (k cs'))
      | match' (Plus (r1, r2)) cs k =
        (match' r1 cs k) orelse (match' r2 cs k)
      | match' (Times (r1, r2)) cs k =
        match' r1 cs (fn cs' => match' r2 cs' k)
      | match' (r as Star r1) cs k =
        (k cs) orelse match' r1 cs (fn cs' => match' r cs' k)

    fun match regexp string =
        match' regexp (String.explode string) (fn nil => true | _ => false)

end

structure HOMatcher :> MATCHER =
struct

    structure RegExp = RegExp
    open RegExp

    fun FAIL cs k = false
    fun NULL cs k = k cs
    fun LITERALLY c cs k = case cs of nil => false | c'::cs' => (c=c') andalso (k cs')
    fun OR (m1, m2) cs k = m1 cs k orelse m2 cs k
    infix 8 OR
    fun THEN (m1, m2) cs k = m1 cs (fn cs' => m2 cs' k)
    infix 9 THEN
    fun REPEATEDLY m cs k = (NULL OR (m THEN (REPEATEDLY m))) cs k

    fun match' Zero = FAIL
      | match' One = NULL
      | match' (Char c) = LITERALLY c
      | match' (Plus (r1, r2)) = match' r1  OR  match' r2
      | match' (Times (r1, r2)) = match' r1  THEN  match' r2
      | match' (Star r) = REPEATEDLY (match' r)

    fun match regexp string =
        match' regexp (String.explode string) (fn nil => true | _ => false)

end
