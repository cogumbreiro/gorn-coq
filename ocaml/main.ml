module Html = Dom_html

open List
open Printf
open String
open Stringext

let rec int_of_nat x =
    match x with
    | Sj.S n -> 1 + int_of_nat n
    | Sj.O -> 0
    ;;

let rec nat_of_int x =
    if x <= 0 then Sj.O
    else Sj.S (nat_of_int (x - 1))

let string_of_event_t t =
    match t with
    | Sj.FORK -> "FORK"
    | Sj.JOIN -> "JOIN"
    ;;

let event_type_of_string s =
    let s = String.uppercase s in
    if s = "FORK" then Some Sj.FORK else
    (if s = "JOIN" then Some Sj.JOIN else None)
    ;;

let trim_parens s : string =
    match split s '(' with
    | _::s::[] ->
        (match split s ')' with
        | s::_::[] -> s
        | _ -> "")
    | _ -> ""

let event_of_string s =
    let s = trim_parens s in
    try (
        match split s ',' with
        | s_src::s_evt::s_dst::[] ->
            let src = int_of_string (trim s_src) in
            let dst = int_of_string (trim s_dst) in
            let evt = event_type_of_string (trim s_evt) in
            (match evt with
            | Some t ->
                Some {Sj.op_t=t;Sj.op_src=nat_of_int src;Sj.op_dst=nat_of_int dst}
            | _ -> None)
        | _ -> None
    ) with
    | _ -> None  

let filter_duplicates lst =
  let rec is_member n mlst =
    match mlst with
    | [] -> false
    | h::tl ->
        begin
          if h=n then true
          else is_member n tl
        end
  in
  let rec loop lbuf =
    match lbuf with
    | [] -> []
    | h::tl ->
        begin
        let rbuf = loop tl
        in
          if is_member h rbuf then rbuf
          else h::rbuf
        end
  in
  loop lst

let string_of_event e =
    let n1 = (int_of_nat (Sj.op_src e)) in
    let n2 = (int_of_nat (Sj.op_dst e)) in
    let n1, n2 = match Sj.op_t e with
    | Sj.FORK -> (n1, n2)
    | Sj.JOIN -> (n2, n1)
    in
    Printf.sprintf "%d -> %d [label=%s]" n1 n2 (string_of_event_t (Sj.op_t e));;

let rec from_list l =
    match l with
    | [] -> Sj.Nil
    | x::xs -> Sj.Cons (x,from_list xs)
    ;;

let trace_of_string s =
    let to_evt x : Sj.op list = match (event_of_string x) with
        | Some x -> [x]
        | _ -> []
    in
    from_list (rev (flatten (List.map to_evt (split s '\n'))))

let rec as_list l : 'a list =
    match l with
    | Sj.Cons (x, l) ->
        x::(as_list l)
    | _ -> []

let rec string_of_trace (t:Sj.op Sj.list) :  string =
    concat "\n" (rev (List.map string_of_event (as_list t)))

let string_of_edge e =
    match e with
    | Sj.Pair (x,y) -> Printf.sprintf "%d -> %d [label=KNOWS]" (int_of_nat x) (int_of_nat y)
    ;;    

let string_of_graph es =
    concat "\n" (List.map string_of_edge (filter_duplicates (as_list es)))

let print_is_safe t = match Sj.is_safe t with
    | Sj.None -> ""
    | Sj.Some es -> string_of_graph es
    ;;

let to_dot t =
    let lines = [
        "digraph G {";
        print_is_safe t;
(*        string_of_trace t;*)
        "}"
    ] in
    String.concat "\n" lines

let update_network container s =
    let convert_dot s =
        Js.Unsafe.fun_call (Js.Unsafe.js_expr "vis.network.convertDot")
        [|Js.Unsafe.inject s|] in

    let opts = Js.Unsafe.js_expr "{
  layout:{
    randomSeed: 0,
  },
  physics: {
    enabled: true,
    solver: 'forceAtlas2Based'
  }
}
" in    
    (* var network = new vis.Network(container, data, options); *)
    Js.Unsafe.new_obj (Js.Unsafe.variable "vis.Network")
    [| Js.Unsafe.inject container;  Js.Unsafe.inject (convert_dot s); opts|];
    Js._false 

let onload _ =
    let txt =
        Dom_html.getElementById "trace_in"
        |> Dom_html.CoerceTo.textarea
        |> fun opt ->
        Js.Opt.case opt 
        (fun () -> assert false)
        (fun div -> div)
    in
    let graph =
        Js.Opt.get (Html.document##getElementById(Js.string "graph_out"))
        (fun () -> assert false) in
    txt##onkeyup <- Html.handler (
        fun _ ->
        let trace_txt = Js.to_string (txt##value) in
        let t = trace_of_string trace_txt in
        let dot = Js.string (to_dot t) in
        update_network graph dot;
        Js._false
    );
    Js._false

let _ =
    Html.window##onload <- Html.handler onload

