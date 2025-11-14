open Js_of_ocaml

let unlines lines =
  match lines with
  | [] -> ""
  | _ -> String.concat "\n" lines

let to_lines source =
  if String.equal source "" then [] else String.split_on_char '\n' source

let run_processor source =
  let lines = to_lines source in
  try Ok (Expect.process_lines ~filename:"<buffer>" lines) with
  | Expect.Error msg -> Error msg
  | exn ->
      let msg = Printexc.to_string exn in
      Error msg

let encode_result = function
  | Ok lines ->
      let obj = Js.Unsafe.obj [||] in
      Js.Unsafe.set obj "ok" Js._true;
      Js.Unsafe.set obj "output" (Js.string (unlines lines));
      obj
  | Error msg ->
      let obj = Js.Unsafe.obj [||] in
      Js.Unsafe.set obj "ok" Js._false;
      Js.Unsafe.set obj "error" (Js.string msg);
      obj

let () =
  Printexc.record_backtrace true;
  let api =
    object%js
      method process payload =
        let source = Js.to_string payload in
        encode_result (run_processor source)
    end
  in
  Js.Unsafe.set Js.Unsafe.global "MoxPlayground" api
