open Lexing

let position pos =
  let file = pos.pos_fname in
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  Printf.sprintf "file \"%s\", line %d, character %d" file l c

let positions pos1 pos2 =
  let file = pos1.pos_fname in
  let line = pos1.pos_lnum in
  let char1 = pos1.pos_cnum - pos1.pos_bol + 1 in
  let char2 = pos2.pos_cnum - pos1.pos_bol + 1 in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d" file line char1 char2
