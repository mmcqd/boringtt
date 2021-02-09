open Core

type 'a t = 'a String.Map.t

let (++) g (key,data) = String.Map.set g ~key ~data

let find = String.Map.find
let find_exn = String.Map.find_exn
let key_set = String.Map.key_set
let mapi = String.Map.mapi
let empty = String.Map.empty
let map = String.Map.map
