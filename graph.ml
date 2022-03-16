let empty () = Hashtbl.create 30097

let mem graph x = Hashtbl.mem graph x

let add graph x y =
  if not (Hashtbl.mem graph x) then
    Hashtbl.add graph x y

let find graph x = Hashtbl.find graph x
