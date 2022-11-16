(* Wiedza dla jakiegoś punktu (instrukcji, bloku, terminatora) *)
module Knowledge = struct
  (* wierdza na wejściu (pre) oraz wyjściu (post)*)
  type 'a t = { pre : 'a; post : 'a }

  (* akcesory *)

  let pre t = t.pre
  let post t = t.post

  let alter ?pre ?post t =
    let t = match pre with Some pre -> { t with pre } | None -> t in
    let t = match post with Some post -> { t with post } | None -> t in
    t

  (* konstruktor *)

  let make ~pre ~post : 'a t = { pre; post }

  (* alias *)

  type 'a table = (Ir.label, 'a t) Hashtbl.t
end

(* Wiedza o wierzcholku w grafie sterowania *)
module BlockKnowledge = struct
  (* 
   * Simple - mamy tylko wiedzę na wejściu/wyjściu
   *   - używane w analizach co nie interesują się instrukcjami (jak analiza dominacji)
   *     lub przy wyszczególnioncyh wierzchołkach entry/exit.
   * Complex - mamy wiedzę o instrukcjach wewnątrz bloku
   *   - block - wiedza na wejściu wyjściu do bloku
   *   - body - lista instrukcji bloku wraz z wiedzą
   *   - terminator - terminator bloku wraz z wiedzą
   *)
  type 'a t =
    | Simple of 'a Knowledge.t
    | Complex of {
        block : 'a Knowledge.t;
        body : ('a Knowledge.t * Ir.instr) list;
        terminator : 'a Knowledge.t * Ir.terminator;
      }

  (* akcesory *)

  (* zwraca wiedzę Knowledge dla całego bloku
   *   - działa z dwoma konstruktorami *)
  let block = function Simple t -> t | Complex { block; _ } -> block

  (* zwracają pola pre/post z wiedzy dla całego bloku
   *   - działa z dwoma konstruktorami *)

  let pre t = Knowledge.pre @@ block t
  let post t = Knowledge.post @@ block t

  (* zwraca terminator i wiedzę na jego temat, działa tylko z Complex *)
  let terminator = function
    | Simple _ -> failwith "BlockKnowledge.terminator"
    | Complex t -> t.terminator

  (* zwraca listę instrukcji wraz z wiedzą na ich temat, działa tylko z Complex *)
  let body = function
    | Simple _ -> failwith "BlockKnowledge.body"
    | Complex t -> t.body

  (* zwraca terminator, działa tylko z Complex *)
  let terminator_instr t = snd @@ terminator t

  (* zwraca wiedzę o terminatorze, działa tylko z Complex *)
  let terminator_kw t = fst @@ terminator t

  (* setter wiedzy o całym bloku, działa z dwoma konstruktorami *)
  let alter_prepost ?pre ?post = function
    | Simple t -> Simple (Knowledge.alter ?pre ?post t)
    | Complex { block; body; terminator } ->
        let block = Knowledge.alter ?pre ?post block in
        Complex { block; body; terminator }

  let is_complex = function Complex _ -> true | Simple _ -> false

  (* konstruktory *)

  let make_complex ~block ~body ~terminator =
    Complex { block; body; terminator }

  let make_simple t = Simple t

  (* alias *)

  type 'a table = (Ir.label, 'a t) Hashtbl.t
end
