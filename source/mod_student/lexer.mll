{
  (* Standardowo w YACC-podobnych narzędziach to lekser jest uzależniony od parsera.
   * To znaczy, że typ danych z tokenami definiuje moduł wygenerowany na bazie parser.mly.
   *)
  open Zi_lib
  open Parser
  open Parser_utils

  (* Lexing z biblioteki standardowej ocamla *)
  open Lexing

  (* Definiujemy alias na typ tokenu na potrzeby interfejsów Zi_lib.Iface *)
  type token = Parser.token

  (* Obsługa błędu *)
  let handleError lexbuf =
      let pos = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
      let token = Lexing.lexeme lexbuf in
      let exc = InvalidToken (mkLocation pos, token) in
      raise exc
      
  (* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv 
   * Miejsce na twój kod w Ocamlu
   *)


  (* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
     ----------------------------------------------------------------------------- *)

  }
  
  (* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv 
   * Miejsce na nazwane wyrażenia regularne
   *)

  let identifier    = ['_' 'a'-'z' 'A'-'Z']['_' 'A'-'Z' 'a'-'z' '0'-'9' ''']*
  
  (* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
     ----------------------------------------------------------------------------- *)


  rule token = parse
      (* Trzeba pamiętać aby uaktualnić pozycje w lexbuf, gdy widzimy znak końca wiersza.
       * To się samo nie robi. Moduł Lexing z standardowej biblioteki daje do tego wygodną
       * funkcję new_line.
       *)
      | ['\n']
      { new_line lexbuf; token lexbuf }

      (* widzimy początek komentarza i przechodzimy do pomocniczego stanu *)
      | "//"
      { line_comment lexbuf }

      | eof
      { EOF }

      (* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv 
       * Miejsce na twoje reguły
       *)

      | identifier as id
      { failwith id }

      (* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
         ----------------------------------------------------------------------------- *)
  
      | _
      { handleError lexbuf }

  (* Pomocniczy stan aby wygodnie i prawidłowo obsłużyć komentarze *)
  and line_comment = parse
      | '\n' 
      { new_line lexbuf; token lexbuf }

      (* Niektóre edytory nie wstawiają znaku końca wiersza w ostatniej linijce, jesteśmy
       * przygotowani na obsługę takiego komentarza.
       *)
      | eof
      { EOF }

      | _ 
      { line_comment lexbuf }
